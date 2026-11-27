-- Prove2me | solution 1 for ECDLP.point_group_structure
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T22:13:33.691301+00:00
-- url     : https://prove2.me/submissions/1882545c-deaa-4d5c-94bb-d89cff2c9e94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_LefebvreVariations_elliptic_prime_torsion_card_le
set_option autoImplicit false

universe u

private def Kn (G : Type*) [AddCommGroup G] (n : ℕ) : AddSubgroup G where
  carrier := {g | n • g = 0}
  add_mem' := by intro a b ha hb; simp_all [smul_add]
  zero_mem' := by simp
  neg_mem' := by intro a ha; simp_all

private lemma mem_Kn {G : Type*} [AddCommGroup G] (n : ℕ) (g : G) : g ∈ Kn G n ↔ n • g = 0 := Iff.rfl

private lemma card_Kn_mul {G : Type*} [AddCommGroup G] [Finite G] (a b : ℕ) :
    Nat.card (Kn G (a * b)) ≤ Nat.card (Kn G a) * Nat.card (Kn G b) := by
  let φ : Kn G (a * b) →+ Kn G a :=
    { toFun := fun x => ⟨b • (x : G), by
        have := x.2; rw [mem_Kn] at this ⊢; rw [← mul_nsmul, mul_comm]; exact this⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [smul_add] }
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have h2 : Nat.card (Kn G (a * b) ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
  have h3 : Nat.card φ.range ≤ Nat.card (Kn G a) := Nat.card_le_card_of_injective _ Subtype.val_injective
  have h4 : Nat.card φ.ker ≤ Nat.card (Kn G b) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : Kn G (a*b)) : G), ?_⟩) ?_
    · have := x.2; rw [AddMonoidHom.mem_ker] at this
      have h := congrArg Subtype.val this
      simpa [φ, mem_Kn] using h
    · intro x y hxy; ext; simpa using congrArg Subtype.val hxy
  rw [h1, h2]
  exact Nat.mul_le_mul h3 h4

private lemma card_bound_all {G : Type*} [AddCommGroup G] [Finite G] (k : ℕ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → Nat.card {g : G // ℓ • g = 0} ≤ ℓ ^ k) :
    ∀ n : ℕ, 0 < n → Nat.card {g : G // n • g = 0} ≤ n ^ k := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; omega
  | one =>
    intro _
    have : Nat.card (Kn G 1) ≤ 1 := by
      have : Subsingleton (Kn G 1) := ⟨fun x y => by
        have hx := x.2; have hy := y.2; rw [mem_Kn] at hx hy; simp at hx hy
        ext; rw [hx, hy]⟩
      exact Finite.card_le_one_iff_subsingleton.mpr this
    simpa using this
  | prime p hp => intro _; exact h p hp
  | mul a b iha ihb =>
    intro hab
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hab)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab)
    have := card_Kn_mul (G := G) a b
    calc Nat.card {g : G // (a*b) • g = 0} = Nat.card (Kn G (a*b)) := rfl
      _ ≤ Nat.card (Kn G a) * Nat.card (Kn G b) := this
      _ ≤ a ^ k * b ^ k := Nat.mul_le_mul (iha ha) (ihb hb)
      _ = (a*b)^k := (mul_pow a b k).symm

private lemma exists_complement {G : Type*} [AddCommGroup G] [Finite G] (g : G)
    (hg : ∀ x : G, addOrderOf g • x = 0) :
    ∃ H : AddSubgroup G, Disjoint (AddSubgroup.zmultiples g) H ∧
      AddSubgroup.zmultiples g ⊔ H = ⊤ := by
  classical
  set C := AddSubgroup.zmultiples g with hC
  set m := addOrderOf g with hm
  have hmpos : 0 < m := addOrderOf_pos g
  obtain ⟨H, hHS, hHmax⟩ := (wellFounded_gt (α := AddSubgroup G)).has_min
    {H : AddSubgroup G | Disjoint C H} ⟨⊥, disjoint_bot_right⟩
  have hHd : Disjoint C H := hHS
  refine ⟨H, hHd, ?_⟩
  by_contra hne
  have hdis : ∀ z, z ∈ C → z ∈ H → z = 0 := fun z hz hz' =>
    (AddSubgroup.disjoint_def.mp hHd) hz hz'
  obtain ⟨x0, hx0⟩ : ∃ x0 : G, x0 ∉ C ⊔ H := by
    by_contra hall; push_neg at hall
    exact hne ((AddSubgroup.eq_top_iff' _).mpr hall)
  have hq0 : (x0 : G ⧸ (C ⊔ H)) ≠ 0 := by
    intro h; exact hx0 ((QuotientAddGroup.eq_zero_iff _).mp h)
  have hord1 : addOrderOf (x0 : G ⧸ (C ⊔ H)) ≠ 1 := by
    intro h; exact hq0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
  set ℓ := (addOrderOf (x0 : G ⧸ (C ⊔ H))).minFac with hℓ
  have hℓp : ℓ.Prime := Nat.minFac_prime hord1
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hdvd : ℓ ∣ Nat.card (G ⧸ (C ⊔ H)) :=
    (Nat.minFac_dvd _).trans (addOrderOf_dvd_natCard _)
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' (G := G ⧸ (C ⊔ H)) ℓ hdvd
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hx : x ∉ C ⊔ H := by
    intro h
    have : (x : G ⧸ (C ⊔ H)) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr h
    rw [this, addOrderOf_zero] at hq
    exact hℓp.one_lt.ne hq
  have hℓx : ℓ • x ∈ C ⊔ H := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul]
    exact hq ▸ (addOrderOf_nsmul_eq_zero _)
  have hℓm : ℓ ∣ m := by
    by_contra hnd
    have hcop : Nat.Coprime ℓ m := (Nat.Prime.coprime_iff_not_dvd hℓp).mpr hnd
    have hmx : m • x = 0 := hg x
    -- x = u * (ℓ x) + v * (m x)
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ℓ + v * m = 1 := by
      have := Nat.isCoprime_iff_coprime.mpr hcop
      obtain ⟨u, v, h⟩ := this
      exact ⟨u, v, h⟩
    apply hx
    have : x = u • (ℓ • x) + v • (m • x) := by
      rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, huv, one_smul]
    rw [this, hmx, smul_zero, add_zero]
    exact AddSubgroup.zsmul_mem _ hℓx u
  obtain ⟨m', hm'⟩ := hℓm
  obtain ⟨c, hcC, h, hhH, hch⟩ := AddSubgroup.mem_sup.mp hℓx
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hcC
  -- m' • c = 0
  have hm'c : m' • c = 0 := by
    have h1 : m' • (ℓ • x) = 0 := by
      rw [smul_smul, mul_comm, ← hm']; exact hg x
    rw [← hch, smul_add] at h1
    have h2 : m' • c = -(m' • h) := eq_neg_of_add_eq_zero_left h1
    have h3 : m' • c ∈ H := by rw [h2]; exact H.neg_mem (H.nsmul_mem hhH _)
    exact hdis _ (C.nsmul_mem hcC _) h3
  have hℓk : (ℓ : ℤ) ∣ k := by
    have h1 : ((m' : ℤ) * k) • g = 0 := by
      rw [← hk] at hm'c; rw [← natCast_zsmul, smul_smul] at hm'c; exact hm'c
    have h2 := (addOrderOf_dvd_iff_zsmul_eq_zero (x := g) (i := (m' : ℤ) * k)).mpr h1
    rw [← hm, hm'] at h2
    have hm'pos : (0 : ℤ) < m' := by
      have : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)
      exact_mod_cast this
    have h3 : ((ℓ : ℤ) * m') ∣ (m' : ℤ) * k := by push_cast at h2; exact h2
    rw [mul_comm (ℓ : ℤ) m'] at h3
    exact (mul_dvd_mul_iff_left hm'pos.ne').mp h3
  obtain ⟨k', rfl⟩ := hℓk
  set y : G := x - k' • g with hy
  have hc' : ℓ • (k' • g) = c := by rw [← hk, ← natCast_zsmul, smul_smul]
  have hℓy : ℓ • y = h := by
    rw [hy, smul_sub, hc', ← hch]; abel
  have hyCH : y ∉ C ⊔ H := by
    intro hyin
    apply hx
    have : x = y + k' • g := by rw [hy]; abel
    rw [this]
    exact AddSubgroup.add_mem _ hyin
      (AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples_iff.mpr ⟨k', rfl⟩))
  set H' : AddSubgroup G := H ⊔ AddSubgroup.zmultiples y with hH'
  have hS : Disjoint C H' := by
    rw [AddSubgroup.disjoint_def]
    intro z hzC hzH'
    obtain ⟨h', hh', w, hw, hzw⟩ := AddSubgroup.mem_sup.mp hzH'
    obtain ⟨t, ht⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
    by_cases hdt : (ℓ : ℤ) ∣ t
    · obtain ⟨s, rfl⟩ := hdt
      have hwH : w ∈ H := by
        rw [← ht, mul_comm, ← smul_smul, natCast_zsmul, hℓy]
        exact AddSubgroup.zsmul_mem _ hhH s
      exact hdis z hzC (by rw [← hzw]; exact AddSubgroup.add_mem _ hh' hwH)
    · exfalso
      have hcop : IsCoprime t (ℓ : ℤ) :=
        ((Nat.prime_iff_prime_int.mp hℓp).irreducible.coprime_iff_not_dvd.mpr hdt).symm
      obtain ⟨u, v, huv⟩ := hcop
      apply hyCH
      have hty : t • y = z - h' := by rw [ht, ← hzw]; abel
      have : y = u • (z - h') + v • h := by
        rw [← hty, ← hℓy, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, huv, one_smul]
      rw [this]
      exact AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.sub_mem _ (AddSubgroup.mem_sup_left hzC) 
          (AddSubgroup.mem_sup_right hh')) u)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_sup_right hhH) v)
  apply hHmax H' hS
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  apply hyCH
  have : y ∈ H' := AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples y)
  rw [← heq] at this
  exact AddSubgroup.mem_sup_right this

private lemma cyclic_of_prime_bound {H : Type*} [AddCommGroup H] [Finite H]
    (h : ∀ ℓ : ℕ, ℓ.Prime → Nat.card {x : H // ℓ • x = 0} ≤ ℓ) : IsAddCyclic H := by
  classical
  haveI := Fintype.ofFinite H
  refine isAddCyclic_of_card_nsmul_eq_zero_le (fun n hn => ?_)
  have := card_bound_all (G := H) 1 (by simpa using h) n hn
  rw [pow_one, Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  exact this

private lemma prime_bound_complement {G : Type*} [AddCommGroup G] [Finite G]
    (h : ∀ ℓ : ℕ, ℓ.Prime → Nat.card {g : G // ℓ • g = 0} ≤ ℓ ^ 2)
    (g : G) (hg : ∀ x : G, addOrderOf g • x = 0) (H : AddSubgroup G)
    (hd : Disjoint (AddSubgroup.zmultiples g) H) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card {x : H // ℓ • x = 0} ≤ ℓ := by
  classical
  set C := AddSubgroup.zmultiples g with hCdef
  have hcoe : ∀ z : {x : H // ℓ • x = 0}, ℓ • ((z.1 : H) : G) = 0 := fun z => by
    have := congrArg (fun y : H => (y : G)) z.2
    simpa using this
  by_cases hdv : ℓ ∣ addOrderOf g
  · haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hdvC : ℓ ∣ Nat.card C := by rwa [hCdef, Nat.card_zmultiples]
    obtain ⟨u, hu⟩ := exists_prime_addOrderOf_dvd_card' (G := C) ℓ hdvC
    have hu' : addOrderOf (u : G) = ℓ := by rw [AddSubgroup.addOrderOf_coe]; exact hu
    have hℓu : ℓ • (u : G) = 0 := by rw [← hu']; exact addOrderOf_nsmul_eq_zero _
    have hle : AddSubgroup.zmultiples (u : G) ≤ C := (AddSubgroup.zmultiples_le).mpr u.2
    let Φ : AddSubgroup.zmultiples (u : G) × {x : H // ℓ • x = 0} → {g : G // ℓ • g = 0} :=
      fun p => ⟨(p.1 : G) + ((p.2.1 : H) : G), by
        rw [smul_add, hcoe p.2, add_zero]
        obtain ⟨a, ha⟩ := p.1
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
        show ℓ • (k • (u : G)) = 0
        rw [smul_comm, hℓu, smul_zero]⟩
    have hinj : Function.Injective Φ := by
      rintro ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ ⟨⟨a', ha'⟩, ⟨x', hx'⟩⟩ hab
      have hab' : a + (x : G) = a' + (x' : G) := congrArg Subtype.val hab
      have haC : a - a' ∈ C := C.sub_mem (hle ha) (hle ha')
      have hxH : (x' : G) - x ∈ H := H.sub_mem x'.2 x.2
      have heq : a - a' = (x' : G) - x :=
        sub_eq_sub_iff_add_eq_add.mpr (by rw [hab', add_comm])
      have h0 : a - a' = 0 := (AddSubgroup.disjoint_def.mp hd) haC (heq ▸ hxH)
      have h1 : a = a' := sub_eq_zero.mp h0
      have h2 : (x' : G) - x = 0 := heq ▸ h0
      have h3 : x = x' := Subtype.ext (sub_eq_zero.mp h2).symm
      subst h1; subst h3; rfl
    have hcard := Nat.card_le_card_of_injective Φ hinj
    rw [Nat.card_prod, Nat.card_zmultiples, hu'] at hcard
    have := hcard.trans (h ℓ hℓ)
    rw [pow_two] at this
    exact Nat.le_of_mul_le_mul_left this hℓ.pos
  · have hsub : Subsingleton {x : H // ℓ • x = 0} := by
      have key : ∀ z : {x : H // ℓ • x = 0}, ((z.1 : H) : G) = 0 := by
        intro z
        have hdvd1 : addOrderOf ((z.1 : H) : G) ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero (hcoe z)
        have hdvd2 : addOrderOf ((z.1 : H) : G) ∣ addOrderOf g :=
          addOrderOf_dvd_of_nsmul_eq_zero (hg _)
        rcases (Nat.dvd_prime hℓ).mp hdvd1 with h1 | h1
        · exact AddMonoid.addOrderOf_eq_one_iff.mp h1
        · exact absurd (h1 ▸ hdvd2) hdv
      exact ⟨fun x y => Subtype.ext (Subtype.ext (by rw [key x, key y]))⟩
    exact (Finite.card_le_one_iff_subsingleton.mpr hsub).trans hℓ.one_lt.le

private theorem rank_two_structure {G : Type*} [AddCommGroup G] [Finite G]
    (h : ∀ ℓ : ℕ, ℓ.Prime → Nat.card {g : G // ℓ • g = 0} ≤ ℓ ^ 2) :
    ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ 0 < n₂ ∧ n₁ ∣ n₂ ∧ Nonempty (ZMod n₁ × ZMod n₂ ≃+ G) := by
  classical
  have hmpos : 0 < AddMonoid.exponent G :=
    Nat.pos_of_ne_zero AddMonoid.exponent_ne_zero_of_finite
  obtain ⟨g, hgm⟩ := AddMonoid.exists_addOrderOf_eq_exponent
    (AddMonoid.ExponentExists.of_finite (G := G))
  have hg' : ∀ x : G, AddMonoid.exponent G • x = 0 := fun x => AddMonoid.exponent_nsmul_eq_zero x
  have hg : ∀ x : G, addOrderOf g • x = 0 := fun x => by rw [hgm]; exact hg' x
  obtain ⟨H, hd, hsup⟩ := exists_complement g hg
  have hcyc : IsAddCyclic H :=
    cyclic_of_prime_bound (fun ℓ hℓ => prime_bound_complement h g hg H hd ℓ hℓ)
  let e : (AddSubgroup.zmultiples g) × H ≃+ G :=
    AddEquiv.ofBijective ((AddSubgroup.zmultiples g).subtype.coprod H.subtype) (by
      constructor
      · rintro ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ ⟨⟨a', ha'⟩, ⟨x', hx'⟩⟩ hab
        have hab' : a + x = a' + x' := by simpa using hab
        have haC : a - a' ∈ AddSubgroup.zmultiples g := AddSubgroup.sub_mem _ ha ha'
        have hxH : x' - x ∈ H := H.sub_mem hx' hx
        have heq : a - a' = x' - x :=
          sub_eq_sub_iff_add_eq_add.mpr (by rw [hab', add_comm])
        have h0 : a - a' = 0 := (AddSubgroup.disjoint_def.mp hd) haC (heq ▸ hxH)
        have h1 : a = a' := sub_eq_zero.mp h0
        have h2 : x' - x = 0 := heq ▸ h0
        have h3 : x = x' := (sub_eq_zero.mp h2).symm
        subst h1; subst h3; rfl
      · intro z
        have hz : z ∈ AddSubgroup.zmultiples g ⊔ H := by rw [hsup]; trivial
        obtain ⟨c, hc, x, hx, hcx⟩ := AddSubgroup.mem_sup.mp hz
        exact ⟨(⟨c, hc⟩, ⟨x, hx⟩), by simpa using hcx⟩)
  have hC : Nat.card (AddSubgroup.zmultiples g) = AddMonoid.exponent G := by
    rw [Nat.card_zmultiples, hgm]
  let eC : ZMod (AddMonoid.exponent G) ≃+ AddSubgroup.zmultiples g :=
    (ZMod.ringEquivCongr hC.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv inferInstance)
  let eH : ZMod (Nat.card H) ≃+ H := zmodAddCyclicAddEquiv hcyc
  have hdvd : Nat.card H ∣ AddMonoid.exponent G := by
    obtain ⟨gh, hgh⟩ := hcyc.exists_generator
    rw [← addOrderOf_eq_card_of_forall_mem_zmultiples hgh]
    refine addOrderOf_dvd_of_nsmul_eq_zero (Subtype.ext ?_)
    simpa using hg' (gh : G)
  exact ⟨Nat.card H, AddMonoid.exponent G, Nat.card_pos, hmpos, hdvd,
    ⟨((eH.prodCongr eC).trans AddEquiv.prodComm).trans e⟩⟩




private lemma finite_points {K : Type*} [Field K] [Fintype K] (E : WeierstrassCurve K) :
    Finite E.toAffine.Point := by
  refine Finite.of_injective
    (fun P : E.toAffine.Point => match P with
      | .zero => (none : Option (K × K))
      | .some x y _ => some (x, y)) ?_
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hxy <;> simp_all

theorem solution {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] :
    ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ 0 < n₂ ∧ n₁ ∣ n₂ ∧
      Nonempty (ZMod n₁ × ZMod n₂ ≃+ E.toAffine.Point) := by
  haveI := finite_points E
  obtain ⟨n₁, n₂, h1, h2, h12, ⟨e⟩⟩ :=
    rank_two_structure (G := E.toAffine.Point) (fun ℓ hℓ => LefebvreVariations.elliptic_prime_torsion_card_le E ℓ hℓ)
  exact ⟨n₁, n₂, h1, h2, h12, ⟨e⟩⟩
