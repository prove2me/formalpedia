-- Prove2me | solution 1 for Castro2006.classification
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T09:28:30.611098+00:00
-- url     : https://prove2.me/submissions/8a555613-9762-44ad-9d4e-9cc1b739e9f1

import Mathlib
import Definitions.Def_Castro2006_classDefs
import Theorems.Thm_Castro2006_burnside
import Theorems.Thm_Castro2006_lema_4_5_2
open CategoryTheory

/-!
Skeleton for `Castro2006.classification` (groups of order p^(n+1) with a cyclic subgroup of
index p). Route: if G has a unique subgroup of order p, `Castro2006.burnside` gives cyclic or
generalised quaternion. Otherwise there is an element `b` of order p outside `K = ⟨a⟩`, so G is a
split extension `K ⋊ ⟨b⟩` with `b a b⁻¹ = a^r`, `r^p ≡ 1 (mod p^n)`, and `Castro2006.lema_4_5_2`
pins down `r`. See docs/investigations/castro_classification_plan.md in the notes folder.
-/

namespace GCClass

/-! ### L1: building the action `φ` (multiplication by a unit `r` with `r^p = 1`). -/
/-- multiplication by `r` (with inverse multiplication by `s`) as a MulAut. -/
def mulByAut (N : ℕ) (r s : ZMod N) (hrs : r * s = 1) : MulAut (Multiplicative (ZMod N)) where
  toFun u := Multiplicative.ofAdd (r * Multiplicative.toAdd u)
  invFun u := Multiplicative.ofAdd (s * Multiplicative.toAdd u)
  left_inv u := by
    change Multiplicative.ofAdd (s * (r * Multiplicative.toAdd u)) = u
    rw [← mul_assoc, mul_comm s r, hrs, one_mul]; rfl
  right_inv u := by
    change Multiplicative.ofAdd (r * (s * Multiplicative.toAdd u)) = u
    rw [← mul_assoc, hrs, one_mul]; rfl
  map_mul' u v := by
    change Multiplicative.ofAdd (r * (Multiplicative.toAdd u + Multiplicative.toAdd v)) = _
    rw [mul_add]; rfl

theorem mulByAut_pow (N : ℕ) (r s : ZMod N) (hrs : r * s = 1) (k : ℕ) (u : ZMod N) :
    (mulByAut N r s hrs ^ k) (Multiplicative.ofAdd u) = Multiplicative.ofAdd (r ^ k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    change Multiplicative.ofAdd (r * (r ^ k * u)) = _
    rw [pow_succ', mul_assoc]

theorem exists_action (p m : ℕ) (hp : p.Prime) (r : ZMod (p ^ m)) (hr : r ^ p = 1) :
    ∃ φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ m))),
      ∀ u : ZMod (p ^ m), φ (Multiplicative.ofAdd 1) (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd (r * u) := by
  have hrs : r * r ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hr]
  set σ := mulByAut (p ^ m) r (r ^ (p - 1)) hrs
  have hσ : σ ^ p = 1 := by
    ext u
    obtain ⟨v, rfl⟩ : ∃ v : ZMod (p ^ m), Multiplicative.ofAdd v = u := ⟨Multiplicative.toAdd u, rfl⟩
    rw [mulByAut_pow, hr, one_mul]; rfl
  let f : ℤ →+ Additive (MulAut (Multiplicative (ZMod (p ^ m)))) :=
    zmultiplesHom _ (Additive.ofMul σ)
  have hf : f p = 0 := by
    simp only [f, zmultiplesHom_apply, natCast_zsmul]
    rw [← ofMul_pow, hσ]; rfl
  let g : ZMod p →+ Additive (MulAut (Multiplicative (ZMod (p ^ m)))) := ZMod.lift p ⟨f, hf⟩
  refine ⟨AddMonoidHom.toMultiplicativeLeft g, fun u => ?_⟩
  have h1 : g 1 = Additive.ofMul σ := by
    have := ZMod.lift_coe p ⟨f, hf⟩ 1
    rw [Int.cast_one] at this
    rw [this]; simp [f]
  change (Additive.toMul (g 1)) (Multiplicative.ofAdd u) = _
  rw [h1]; rfl

/-! ### L2: recognising a split extension as an external semidirect product. -/
/-- the hom `Multiplicative (ZMod N) →* G` sending `ofAdd 1` to `x`, when `x ^ N = 1`. -/
def semidirect_recognition_hom {G : Type} [Group G] (N : ℕ) (x : G) (hx : x ^ N = 1) :
    Multiplicative (ZMod N) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift N ⟨zmultiplesHom _ (Additive.ofMul x), by
      simp only [zmultiplesHom_apply, natCast_zsmul]
      rw [← ofMul_pow, hx]; rfl⟩)

theorem semidirect_recognition_hom_int {G : Type} [Group G] (N : ℕ) (x : G) (hx : x ^ N = 1)
    (k : ℤ) : semidirect_recognition_hom N x hx (Multiplicative.ofAdd (k : ZMod N)) = x ^ k := by
  change Additive.toMul (ZMod.lift N _ (k : ZMod N)) = _
  rw [ZMod.lift_coe]
  simp [zmultiplesHom_apply]

theorem semidirect_recognition_hom_nat {G : Type} [Group G] (N : ℕ) (x : G) (hx : x ^ N = 1)
    (k : ℕ) : semidirect_recognition_hom N x hx (Multiplicative.ofAdd (k : ZMod N)) = x ^ k := by
  have := semidirect_recognition_hom_int N x hx k
  rw [Int.cast_natCast, zpow_natCast] at this
  exact this

theorem semidirect_recognition {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Fintype G] (n : ℕ)
    (hcard : Fintype.card G = p ^ (n + 1)) (a b : G) (ha : orderOf a = p ^ n)
    (hb : orderOf b = p) (hbK : b ∉ Subgroup.zpowers a) (r : ℕ) (hrel : b * a * b⁻¹ = a ^ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ n))))
    (hφ : ∀ u : ZMod (p ^ n), φ (Multiplicative.ofAdd 1) (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd ((r : ZMod (p ^ n)) * u)) :
    Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod (p ^ n)))
      (Multiplicative (ZMod p)) φ) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have ha1 : a ^ (p ^ n) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb1 : b ^ p = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  set ψ := semidirect_recognition_hom (p ^ n) a ha1 with hψdef
  set χ := semidirect_recognition_hom p b hb1 with hχdef
  have hψ : ∀ k : ℕ, ψ (Multiplicative.ofAdd (k : ZMod (p ^ n))) = a ^ k :=
    semidirect_recognition_hom_nat _ a ha1
  have hχ : ∀ k : ℕ, χ (Multiplicative.ofAdd (k : ZMod p)) = b ^ k :=
    semidirect_recognition_hom_nat _ b hb1
  -- every element of `Multiplicative (ZMod N)` is `ofAdd` of a natural number cast.
  have hrepψ : ∀ u : Multiplicative (ZMod (p ^ n)),
      u = Multiplicative.ofAdd (((Multiplicative.toAdd u).val : ℕ) : ZMod (p ^ n)) := by
    intro u; rw [ZMod.natCast_zmod_val]; rfl
  have hrepχ : ∀ u : Multiplicative (ZMod p),
      u = Multiplicative.ofAdd (((Multiplicative.toAdd u).val : ℕ) : ZMod p) := by
    intro u; rw [ZMod.natCast_zmod_val]; rfl
  -- key: conjugation by `b` acts on `ψ` as `φ (ofAdd 1)`.
  set σ := φ (Multiplicative.ofAdd 1) with hσ
  have hkey : ∀ v, ψ (σ v) = b * ψ v * b⁻¹ := by
    intro v
    rw [hrepψ v, hσ, hφ]
    set j := (Multiplicative.toAdd v).val
    rw [hψ j, ← Nat.cast_mul, hψ, ← conj_pow, hrel, ← pow_mul]
  have hkeyk : ∀ k : ℕ, ∀ v, ψ ((σ ^ k) v) = b ^ k * ψ v * (b ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', MulAut.mul_apply, hkey, ih, pow_succ']
      group
  have hcompat : ∀ g, ψ.comp (φ g).toMonoidHom = (MulAut.conj (χ g)).toMonoidHom.comp ψ := by
    intro g
    refine MonoidHom.ext fun v => ?_
    show ψ (φ g v) = χ g * ψ v * (χ g)⁻¹
    rw [hrepχ g]
    set k := (Multiplicative.toAdd g).val
    have hg : (Multiplicative.ofAdd ((k : ℕ) : ZMod p)) = (Multiplicative.ofAdd (1 : ZMod p)) ^ k := by
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
    rw [hχ k, hg, map_pow, ← hσ, hkeyk]
  set F := SemidirectProduct.lift ψ χ hcompat with hF
  have hFapp : ∀ x, F x = ψ x.left * χ x.right := fun x => rfl
  have hψmem : ∀ u, ψ u ∈ Subgroup.zpowers a := by
    intro u; rw [hrepψ u, hψ]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hFapp] at hx
    have hχmem : χ x.right ∈ Subgroup.zpowers a := by
      have : χ x.right = (ψ x.left)⁻¹ := eq_inv_of_mul_eq_one_right hx
      rw [this]; exact Subgroup.inv_mem _ (hψmem _)
    have hright : x.right = 1 := by
      rw [hrepχ x.right] at hχmem ⊢
      set j := (Multiplicative.toAdd x.right).val with hj
      rw [hχ j] at hχmem
      by_cases hj0 : j = 0
      · rw [hj0, Nat.cast_zero]; rfl
      exfalso
      have hjlt : j < p := ZMod.val_lt _
      have hc : ¬ p ∣ j := fun h => hj0 (Nat.eq_zero_of_dvd_of_lt h hjlt)
      have hcop : (orderOf b).Coprime j := by
        rw [hb]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hc
      apply hbK
      have hle : Subgroup.zpowers (b ^ j) ≤ Subgroup.zpowers b :=
        Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) j)
      have heq : Subgroup.zpowers (b ^ j) = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge hle
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow])
      have hb' : b ∈ Subgroup.zpowers (b ^ j) := heq ▸ Subgroup.mem_zpowers b
      exact (Subgroup.zpowers_le.2 hχmem) hb'
    rw [hright, map_one, mul_one] at hx
    have hleft : x.left = 1 := by
      rw [hrepψ x.left] at hx ⊢
      set i := (Multiplicative.toAdd x.left).val
      rw [hψ i, ← orderOf_dvd_iff_pow_eq_one, ha] at hx
      rw [(ZMod.natCast_eq_zero_iff i (p ^ n)).2 hx]; rfl
    exact SemidirectProduct.ext hleft hright
  have hcardSD : Nat.card (SemidirectProduct (Multiplicative (ZMod (p ^ n)))
      (Multiplicative (ZMod p)) φ) = p ^ (n + 1) := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, Nat.card_zmod, pow_succ]
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (by rw [hcardSD, Nat.card_eq_fintype_card, hcard])
  exact ⟨(MulEquiv.ofBijective F hbij).symm⟩

/-! ### L3: recognising the dihedral group. -/
theorem dihedral_recognition_pow_add {G : Type} [Group G] (N : ℕ) [NeZero N] (a : G)
    (ha : orderOf a = N) (i j : ZMod N) : a ^ (i.val) * a ^ (j.val) = a ^ ((i + j).val) := by
  subst ha
  rw [← pow_add, ZMod.val_add, pow_mod_orderOf]

theorem dihedral_recognition_pow_sub {G : Type} [Group G] (N : ℕ) [NeZero N] (a : G)
    (ha : orderOf a = N) (i j : ZMod N) : a ^ ((j - i).val) = a ^ (j.val) * (a ^ (i.val))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, dihedral_recognition_pow_add N a ha, sub_add_cancel]

theorem dihedral_recognition_conj {G : Type} [Group G] (a b : G) (hb2 : b * b = 1)
    (hrel : b * a * b⁻¹ = a⁻¹) (k : ℕ) : a ^ k * b = b * (a ^ k)⁻¹ := by
  have hbinv : b⁻¹ = b := (eq_inv_of_mul_eq_one_left hb2).symm
  have h1 : a * b = b * a⁻¹ := by
    rw [← hrel, hbinv]; simp [← mul_assoc, hb2]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, mul_assoc, ← mul_inv_rev, ← pow_succ']
    rw [pow_succ]

/-- the map `DihedralGroup (2^n) → G`. -/
def dihedral_recognition_fun {G : Type} [Group G] (N : ℕ) (a b : G) :
    DihedralGroup N → G
  | DihedralGroup.r i => a ^ (i.val)
  | DihedralGroup.sr i => b * a ^ (i.val)

theorem dihedral_recognition {G : Type} [Group G] [Fintype G] (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card G = 2 ^ (n + 1)) (a b : G) (ha : orderOf a = 2 ^ n)
    (hb : orderOf b = 2) (hbK : b ∉ Subgroup.zpowers a) (hrel : b * a * b⁻¹ = a⁻¹) :
    Nonempty (G ≃* DihedralGroup (2 ^ n)) := by
  have hb2 : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hc := dihedral_recognition_conj a b hb2 hrel
  have hadd := dihedral_recognition_pow_add (2 ^ n) a ha
  have hsub := dihedral_recognition_pow_sub (2 ^ n) a ha
  let f : DihedralGroup (2 ^ n) →* G :=
    { toFun := dihedral_recognition_fun (2 ^ n) a b
      map_one' := by
        change a ^ ((0 : ZMod (2 ^ n)).val) = 1
        simp
      map_mul' := by
        rintro (i | i) (j | j)
        · simp only [DihedralGroup.r_mul_r, dihedral_recognition_fun, hadd]
        · simp only [DihedralGroup.r_mul_sr, dihedral_recognition_fun, hsub]
          rw [← mul_assoc (a ^ i.val), hc, mul_assoc]
          congr 1
          exact (Commute.pow_pow_self a _ _).inv_right.eq
        · simp only [DihedralGroup.sr_mul_r, dihedral_recognition_fun, ← hadd, mul_assoc]
        · simp only [DihedralGroup.sr_mul_sr, dihedral_recognition_fun, hsub]
          rw [mul_assoc, ← mul_assoc (a ^ i.val), hc, ← mul_assoc, ← mul_assoc, hb2, one_mul]
          exact (Commute.pow_pow_self a _ _).inv_left.eq.symm }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) h
    · change a ^ (i.val) = 1 at h
      rw [← orderOf_dvd_iff_pow_eq_one, ha] at h
      have hlt : i.val < 2 ^ n := ZMod.val_lt i
      have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
      rw [ZMod.val_eq_zero] at h0
      rw [h0]; rfl
    · exfalso
      change b * a ^ (i.val) = 1 at h
      apply hbK
      rw [eq_inv_of_mul_eq_one_left h]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [DihedralGroup.card, hcard, pow_succ, mul_comm]
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-! ### L4: group-theoretic setup in the non-unique case. -/
theorem split_setup_conj_pow {G : Type} [Group G] (a b : G) (r : ℕ) (hrel : b * a * b⁻¹ = a ^ r)
    (c : ℕ) : b ^ c * a * (b ^ c)⁻¹ = a ^ (r ^ c) := by
  induction c with
  | zero => simp
  | succ k ih =>
    have h1 : b ^ (k + 1) * a * (b ^ (k + 1))⁻¹ = b * (b ^ k * a * (b ^ k)⁻¹) * b⁻¹ := by
      rw [pow_succ']; group
    rw [h1, ih, ← conj_pow, hrel, ← pow_mul, pow_succ', mul_comm]

theorem split_setup_mem_low {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] (n : ℕ)
    (hn : n ≠ 0) (a : G) (ha : orderOf a = p ^ n) (x : G) (hx : x ∈ Subgroup.zpowers a)
    (hxp : x ^ p = 1) : x ∈ Subgroup.zpowers (a ^ (p ^ (n - 1))) := by
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hx)
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ha] at hxp
  have hpn : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]
  rw [hpn] at hxp
  obtain ⟨m, hm⟩ := Nat.dvd_of_mul_dvd_mul_right hp.pos hxp
  rw [hm, pow_mul]
  exact Subgroup.npow_mem_zpowers _ m

theorem split_setup_le_unique {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] (n : ℕ)
    (a : G) (ha : orderOf a = p ^ n) (H₁ H₂ : Subgroup G) (h₁ : H₁ ≤ Subgroup.zpowers a)
    (h₂ : H₂ ≤ Subgroup.zpowers a) (c₁ : Nat.card H₁ = p) (c₂ : Nat.card H₂ = p) : H₁ = H₂ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    have := Subgroup.card_le_of_le h₁
    rw [c₁, Nat.card_zpowers, ha, pow_zero] at this
    have := hp.two_le
    omega
  set C := Subgroup.zpowers (a ^ (p ^ (n - 1)))
  have hC : Nat.card C = p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero)
      (ha ▸ pow_dvd_pow p (Nat.sub_le n 1)), ha, Nat.pow_div (Nat.sub_le n 1) hp.pos,
      show n - (n - 1) = 1 by omega, pow_one]
  have key : ∀ H : Subgroup G, H ≤ Subgroup.zpowers a → Nat.card H = p → H = C := by
    intro H hH hc
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      apply split_setup_mem_low hp n hn.ne' a ha x (hH hx)
      have := Subgroup.orderOf_dvd_natCard H hx
      rw [hc] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    · rw [hC, hc]
  rw [key H₁ h₁ c₁, key H₂ h₂ c₂]

theorem split_setup {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Fintype G] (n : ℕ)
    (hcard : Fintype.card G = p ^ (n + 1)) (K : Subgroup G) (hKcyc : IsCyclic K)
    (hKidx : K.index = p) (hnu : ¬ ∃! H : Subgroup G, Nat.card H = p) :
    ∃ (a b : G) (r : ℕ), orderOf a = p ^ n ∧ orderOf b = p ∧ b ∉ Subgroup.zpowers a ∧
      b * a * b⁻¹ = a ^ r ∧ (r : ZMod (p ^ n)) ^ p = 1 := by
  classical
  have hFact : Fact p.Prime := ⟨hp⟩
  have hcardG : Nat.card G = p ^ (n + 1) := by rw [Nat.card_eq_fintype_card, hcard]
  have hKcard : Nat.card K = p ^ n := by
    have h := K.index_mul_card
    rw [hKidx, hcardG, pow_succ, mul_comm (p ^ n)] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  obtain ⟨g, hg⟩ := hKcyc.exists_generator
  have hord : orderOf (g : G) = p ^ n := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hKcard]
  have hKa : Subgroup.zpowers (g : G) = K := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.2 g.2
    · rw [hKcard, Nat.card_zpowers, hord]
  have hKn : K.Normal := Subgroup.normal_of_index_eq_minFac_card
    (by rw [hKidx, hcardG, hp.pow_minFac (Nat.succ_ne_zero n)])
  have hex : ∃ H : Subgroup G, Nat.card H = p ∧ ¬ H ≤ K := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G) p
      (by rw [hcard]; exact dvd_pow_self p (Nat.succ_ne_zero n))
    have hx' : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
    by_contra hcon
    push Not at hcon
    apply hnu
    refine ⟨Subgroup.zpowers x, hx', fun H hH => ?_⟩
    rw [← hKa] at hcon
    exact split_setup_le_unique hp n _ hord H _ (hcon H hH) (hcon _ hx') hH hx'
  obtain ⟨H, hHc, hHK⟩ := hex
  obtain ⟨b, hbH, hbK⟩ := SetLike.not_le_iff_exists.1 hHK
  have hb1 : b ≠ 1 := fun h => hbK (h ▸ K.one_mem)
  have hbp : b ^ p = 1 := by
    have := Subgroup.orderOf_dvd_natCard H hbH
    rw [hHc] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hconj : b * (g : G) * b⁻¹ ∈ Subgroup.zpowers (g : G) := by
    rw [hKa]; exact hKn.conj_mem _ g.2 b
  obtain ⟨r, hr⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hconj)
  refine ⟨g, b, r, hord, hbord, by rw [hKa]; exact hbK, hr.symm, ?_⟩
  have h1 := split_setup_conj_pow (g : G) b r hr.symm p
  rw [hbp, one_mul, inv_one, mul_one] at h1
  have h2 : (g : G) ^ (r ^ p) = (g : G) ^ 1 := by rw [pow_one]; exact h1.symm
  rw [pow_eq_pow_iff_modEq, hord] at h2
  have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  push_cast at this
  exact this

/-! ### L5: arithmetic of `r` (uses `Castro2006.lema_4_5_2`). -/
theorem unit_order_p_n1 {p : ℕ} (hp : p.Prime) (r : ℕ) (hr : (r : ZMod (p ^ 1)) ^ p = 1) :
    (r : ZMod (p ^ 1)) = 1 := by
  have hq : p ^ 1 = p := pow_one p
  have : Fact p.Prime := ⟨hp⟩
  revert hr; rw [hq]; intro hr
  rwa [ZMod.pow_card] at hr

theorem unit_normal_form_pkill {p : ℕ} (n : ℕ) (hn : 1 ≤ n) :
    (p : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1) = 0 := by
  rw [← pow_succ', Nat.sub_add_cancel hn, ← Nat.cast_pow, ZMod.natCast_self]

/-- `k * p^(n-1)` only depends on `k` mod `p`. -/
theorem unit_normal_form_shift {p : ℕ} (n : ℕ) (hn : 1 ≤ n) (a j : ℤ) :
    ((a + p * j : ℤ) : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1) =
      (a : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1) := by
  have h := unit_normal_form_pkill (p := p) n hn
  push_cast
  linear_combination (j : ZMod (p ^ n)) * h

theorem unit_normal_form_binom {R : Type*} [CommRing R] (x : R) (hx : x * x = 0) (c : ℕ) :
    (1 + x) ^ c = 1 + c * x := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, ih]; push_cast; linear_combination (c : R) * hx

theorem unit_normal_form_toInt {p : ℕ} (n : ℕ) (a b : ℤ)
    (h : (a : ZMod (p ^ n)) = (b : ZMod (p ^ n))) : a ≡ b [ZMOD (p : ℤ) ^ n] := by
  have := (ZMod.intCast_eq_intCast_iff a b (p ^ n)).1 h
  simpa using this

theorem unit_normal_form {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 2 ≤ n) (r : ℕ)
    (hr : (r : ZMod (p ^ n)) ^ p = 1) (hr1 : (r : ZMod (p ^ n)) ≠ 1) :
    (p ≠ 2 ∧ ∃ c : ℕ, ¬ p ∣ c ∧ (r : ZMod (p ^ n)) ^ c = 1 + (p : ZMod (p ^ n)) ^ (n - 1)) ∨
    (p = 2 ∧ ((r : ZMod (2 ^ n)) = 1 + 2 ^ (n - 1) ∨ (r : ZMod (2 ^ n)) = -1 ∨
      (3 ≤ n ∧ (r : ZMod (2 ^ n)) = -1 + 2 ^ (n - 1)))) := by
  have hn1 : 1 ≤ n := by omega
  have hrI : ((r : ℤ) : ZMod (p ^ n)) = (r : ZMod (p ^ n)) := Int.cast_natCast r
  have hap : (r : ℤ) ^ p ≡ 1 [ZMOD (p : ℤ) ^ n] :=
    unit_normal_form_toInt n _ _ (by push_cast; exact hr)
  have ha1 : ¬ ((r : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ n]) := by
    intro h
    apply hr1
    have := (ZMod.intCast_eq_intCast_iff (r : ℤ) 1 (p ^ n)).2 (by simpa using h)
    rw [← hrI, this, Int.cast_one]
  obtain ⟨hodd, h2⟩ := Castro2006.lema_4_5_2 hp (r : ℤ) n hn hap ha1
  -- general decomposition: r = s + k p^(n-1) in ZMod (p^n)
  have decomp : ∀ s : ℤ, (r : ℤ) ≡ s [ZMOD (p : ℤ) ^ (n - 1)] → ∃ k : ℤ,
      (r : ZMod (p ^ n)) = (s : ZMod (p ^ n)) + (k : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1) := by
    intro s hs
    obtain ⟨k, hk⟩ := (Int.ModEq.dvd hs.symm)
    refine ⟨k, ?_⟩
    rw [← hrI]
    have : (r : ℤ) = s + k * (p : ℤ) ^ (n - 1) := by linear_combination hk
    rw [this]; push_cast; ring
  have hPP : ∀ k : ℤ, ((k : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1)) *
      ((k : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1)) = 0 := by
    intro k
    have hsplit : (p : ZMod (p ^ n)) ^ (n - 1) = (p : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 2) := by
      rw [← pow_succ']; congr 1; omega
    have h := unit_normal_form_pkill (p := p) n hn1
    calc _ = ((k : ZMod (p ^ n)) * k * (p : ZMod (p ^ n)) ^ (n - 2)) *
          ((p : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1)) := by
            rw [hsplit]; ring
      _ = 0 := by rw [h, mul_zero]
  have hmod2 : ∀ k : ℤ, (k : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1) =
      ((k % p : ℤ) : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ (n - 1) := by
    intro k
    conv_lhs => rw [← Int.emod_add_mul_ediv k p]
    exact unit_normal_form_shift n hn1 _ _
  by_cases hp2 : p = 2
  · subst hp2
    right
    refine ⟨rfl, ?_⟩
    have hk2 : ∀ k : ℤ, k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := fun k =>
      Int.emod_two_eq_zero_or_one k
    rcases h2 rfl with hs | hs
    · obtain ⟨k, hk⟩ := decomp 1 (by simpa using hs)
      rw [hmod2] at hk
      rcases hk2 k with h0 | h1
      · exact absurd (by rw [hk, h0]; simp) hr1
      · left; rw [hk, h1]; simp
    · obtain ⟨k, hk⟩ := decomp (-1) (by simpa using hs)
      rw [hmod2] at hk
      rcases hk2 k with h0 | h1
      · right; left; rw [hk, h0]; simp
      · right; right
        refine ⟨?_, by rw [hk, h1]; simp⟩
        by_contra hlt
        have : n = 2 := by omega
        subst this
        apply hr1; rw [hk, h1]; decide
  · left
    refine ⟨hp2, ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := decomp 1 (by simpa using hodd hp2)
    have hk0 : (k : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      obtain ⟨j, hj⟩ := h0
      apply hr1
      rw [hk, hmod2, hj, Int.mul_emod_right]; simp
    set c : ℕ := ((k : ZMod p)⁻¹).val with hc
    have hcz : (c : ZMod p) = (k : ZMod p)⁻¹ := ZMod.natCast_zmod_val _
    refine ⟨c, ?_, ?_⟩
    · intro hdvd
      have : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff c p).2 hdvd
      rw [hcz, inv_eq_zero] at this
      exact hk0 this
    · have hck : (((c : ℤ) * k - 1 : ℤ) : ZMod p) = 0 := by
        push_cast; rw [hcz, inv_mul_cancel₀ hk0, sub_self]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hck
      obtain ⟨j, hj⟩ := hck
      have hck' : (c : ℤ) * k = 1 + p * j := by linear_combination hj
      rw [hk, Int.cast_one, unit_normal_form_binom _ (hPP k)]
      have := unit_normal_form_shift (p := p) n hn1 1 j
      rw [← hck'] at this
      push_cast at this
      rw [one_mul, mul_assoc] at this; rw [this]

/-! ### L6: replacing `b` by `b^c` (p ∤ c). -/
theorem conj_pow_aux {G : Type} [Group G] (a b : G) (r : ℕ) (hrel : b * a * b⁻¹ = a ^ r) (c : ℕ) :
    b ^ c * a * (b ^ c)⁻¹ = a ^ (r ^ c) := by
  induction c with
  | zero => simp
  | succ k ih =>
    have h1 : b ^ (k + 1) * a * (b ^ (k + 1))⁻¹ = b * (b ^ k * a * (b ^ k)⁻¹) * b⁻¹ := by
      rw [pow_succ']; group
    rw [h1, ih, ← conj_pow, hrel, ← pow_mul, pow_succ', mul_comm]

theorem power_twist {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Fintype G] (n : ℕ)
    (a b : G) (_ha : orderOf a = p ^ n) (hb : orderOf b = p) (hbK : b ∉ Subgroup.zpowers a)
    (r : ℕ) (hrel : b * a * b⁻¹ = a ^ r) (c : ℕ) (hc : ¬ p ∣ c) :
    orderOf (b ^ c) = p ∧ b ^ c ∉ Subgroup.zpowers a ∧ b ^ c * a * (b ^ c)⁻¹ = a ^ (r ^ c) := by
  have hcop : (orderOf b).Coprime c := by
    rw [hb]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hc
  refine ⟨by rw [hcop.orderOf_pow, hb], ?_, conj_pow_aux a b r hrel c⟩
  intro hmem
  apply hbK
  have hle : Subgroup.zpowers (b ^ c) ≤ Subgroup.zpowers b :=
    Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) c)
  have heq : Subgroup.zpowers (b ^ c) = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow])
  have hb' : b ∈ Subgroup.zpowers (b ^ c) := heq ▸ Subgroup.mem_zpowers b
  exact (Subgroup.zpowers_le.2 hmem) hb'

/-! ### Assembly helpers (proved). -/

theorem cyclic_case {G : Type} [Group G] [Fintype G] (N : ℕ) (hcard : Fintype.card G = N)
    (hc : IsCyclic G) : Nonempty (G ≃* Multiplicative (ZMod N)) := by
  have hN : Nat.card G = Nat.card (Multiplicative (ZMod N)) := by
    rw [Nat.card_eq_fintype_card, hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact ⟨mulEquivOfCyclicCardEq hN⟩

/-- `a^r = a^s` when `r ≡ s` modulo the order of `a`, stated via `ZMod`. -/
theorem pow_eq_of_cast_eq {G : Type} [Group G] (a : G) (N : ℕ) (ha : orderOf a = N) (r s : ℕ)
    (h : (r : ZMod N) = (s : ZMod N)) : a ^ r = a ^ s := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  rw [← ha] at h
  exact (pow_eq_pow_iff_modEq).2 h

end GCClass

open Castro2006 in
theorem solution {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hcard : Fintype.card G = p ^ (n + 1))
    (K : Subgroup G) (hKcyc : IsCyclic K) (hKidx : K.index = p) :
    Nonempty (G ≃* Multiplicative (ZMod (p ^ (n + 1)))) ∨
    (1 ≤ n ∧ Nonempty (G ≃* Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod p))) ∨
    (2 ≤ n ∧ ∃ φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ n))),
      Castro2006.IsModularAction p n φ ∧
      Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod (p ^ n))) (Multiplicative (ZMod p)) φ)) ∨
    (p = 2 ∧ ((3 ≤ n ∧ Nonempty (G ≃* DihedralGroup (2 ^ n))) ∨
      (2 ≤ n ∧ Nonempty (G ≃* QuaternionGroup (2 ^ (n - 1)))) ∨
      (3 ≤ n ∧ ∃ φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod (2 ^ n))),
        Castro2006.IsSemidihedralAction n φ ∧
        Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod (2 ^ n))) (Multiplicative (ZMod 2)) φ)))) := by
  classical
  -- n = 0: prime order, cyclic.
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have : Fact p.Prime := ⟨hp⟩
    have hc : IsCyclic G := isCyclic_of_prime_card (p := p) (by
      rw [Nat.card_eq_fintype_card, hcard, pow_one])
    exact Or.inl (GCClass.cyclic_case _ hcard hc)
  by_cases hu : ∃! H : Subgroup G, Nat.card H = p
  · -- unique subgroup of order p: Burnside.
    have hpg : IsPGroup p G := IsPGroup.of_card (n := n + 1) (by rw [Nat.card_eq_fintype_card, hcard])
    rcases Castro2006.burnside hp hpg hu with hc | ⟨m, hm, ⟨e⟩⟩
    · exact Or.inl (GCClass.cyclic_case _ hcard hc)
    · have hcQ : Fintype.card G = 4 * 2 ^ m := by
        rw [Fintype.card_congr e.toEquiv, QuaternionGroup.card]
      have h2m : p ^ (n + 1) = 2 ^ (m + 2) := by
        rw [← hcard, hcQ]; ring
      have hp2 : p = 2 := by
        have hdvd : p ∣ 2 ^ (m + 2) := h2m ▸ dvd_pow_self p (Nat.succ_ne_zero n)
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
      subst hp2
      have hnm : n + 1 = m + 2 := Nat.pow_right_injective (le_refl 2) h2m
      have hm' : m = n - 1 := by omega
      subst hm'
      exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨by omega, ⟨e⟩⟩)⟩))
  · -- non-unique: split extension K ⋊ ⟨b⟩.
    obtain ⟨a, b, r, ha, hb, hbK, hrel, hr⟩ := GCClass.split_setup hp n hcard K hKcyc hKidx hu
    by_cases hr1 : (r : ZMod (p ^ n)) = 1
    · -- abelian: K × C_p
      have hrel1 : b * a * b⁻¹ = a ^ (1 : ℕ) := by
        rw [hrel]; exact GCClass.pow_eq_of_cast_eq a _ ha r 1 (by rw [hr1, Nat.cast_one])
      obtain ⟨e⟩ := GCClass.semidirect_recognition hp n hcard a b ha hb hbK 1 hrel1 1
        (fun u => by simp)
      exact Or.inr (Or.inl ⟨hn1, ⟨e.trans SemidirectProduct.mulEquivProd⟩⟩)
    -- nonabelian: n ≥ 2
    have hn2 : 2 ≤ n := by
      by_contra h
      have h1 : n = 1 := by omega
      subst h1
      exact hr1 (GCClass.unit_order_p_n1 hp r hr)
    rcases GCClass.unit_normal_form hp n hn2 r hr hr1 with ⟨_, c, hc, hrc⟩ | ⟨hp2, hcase⟩
    · -- p odd: twist b to b^c, giving the modular action
      obtain ⟨hb', hbK', hrel'⟩ := GCClass.power_twist hp n a b ha hb hbK r hrel c hc
      have hpow : (1 + (p : ZMod (p ^ n)) ^ (n - 1)) ^ p = 1 := by
        rw [← hrc, ← pow_mul, mul_comm, pow_mul, hr, one_pow]
      obtain ⟨φ, hφ⟩ := GCClass.exists_action p n hp _ hpow
      obtain ⟨e⟩ := GCClass.semidirect_recognition hp n hcard a (b ^ c) ha hb' hbK' (r ^ c) hrel' φ
        (fun u => by rw [hφ u, Nat.cast_pow, hrc])
      exact Or.inr (Or.inr (Or.inl ⟨hn2, φ, fun u => hφ u, ⟨e⟩⟩))
    · subst hp2
      rcases hcase with hmod | hneg | ⟨hn3, hsd⟩
      · -- modular, p = 2
        have hpow : (1 + ((2 : ℕ) : ZMod (2 ^ n)) ^ (n - 1)) ^ 2 = 1 := by
          rw [Nat.cast_ofNat, ← hmod, hr]
        obtain ⟨φ, hφ⟩ := GCClass.exists_action 2 n hp _ hpow
        obtain ⟨e⟩ := GCClass.semidirect_recognition hp n hcard a b ha hb hbK r hrel φ
          (fun u => by rw [hφ u, hmod, Nat.cast_ofNat])
        exact Or.inr (Or.inr (Or.inl ⟨hn2, φ, fun u => hφ u, ⟨e⟩⟩))
      · rcases Nat.lt_or_ge n 3 with hlt | hn3
        · -- n = 2: -1 = 1 + 2 in ZMod 4, so this is the modular action (D_8)
          have h2 : n = 2 := by omega
          subst h2
          have hmod : (r : ZMod (2 ^ 2)) = 1 + ((2 : ℕ) : ZMod (2 ^ 2)) ^ (2 - 1) := by
            rw [hneg]; decide
          have hpow : (1 + ((2 : ℕ) : ZMod (2 ^ 2)) ^ (2 - 1)) ^ 2 = 1 := by
            rw [← hmod, hr]
          obtain ⟨φ, hφ⟩ := GCClass.exists_action 2 2 hp _ hpow
          obtain ⟨e⟩ := GCClass.semidirect_recognition hp 2 hcard a b ha hb hbK r hrel φ
            (fun u => by rw [hφ u, hmod])
          exact Or.inr (Or.inr (Or.inl ⟨le_refl 2, φ, fun u => hφ u, ⟨e⟩⟩))
        · -- dihedral
          have hinv : b * a * b⁻¹ = a⁻¹ := by
            rw [hrel]
            have h1 : a ^ (r + 1) = 1 := by
              rw [← pow_orderOf_eq_one a, ha]
              apply GCClass.pow_eq_of_cast_eq a _ ha
              rw [ZMod.natCast_self]; push_cast; rw [hneg]; ring
            rw [pow_succ] at h1
            exact eq_inv_of_mul_eq_one_left h1
          obtain ⟨e⟩ := GCClass.dihedral_recognition n (by omega) hcard a b ha hb hbK hinv
          exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨hn3, ⟨e⟩⟩⟩))
      · -- semidihedral
        obtain ⟨φ, hφ⟩ := GCClass.exists_action 2 n hp _ hr
        obtain ⟨e⟩ := GCClass.semidirect_recognition hp n hcard a b ha hb hbK r hrel φ
          (fun u => hφ u)
        refine Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨hn3, φ, fun u => ?_, ⟨e⟩⟩)⟩))
        rw [hφ u, hsd]
