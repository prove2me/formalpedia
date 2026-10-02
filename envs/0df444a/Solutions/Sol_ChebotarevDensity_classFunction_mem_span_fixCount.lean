-- Prove2me | solution 1 for ChebotarevDensity.classFunction_mem_span_fixCount
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T14:28:09.057375+00:00
-- url     : https://prove2.me/submissions/dad9338b-3c2b-4338-ba4d-2ad266c0b140

import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField

open ChebotarevDensity

private lemma fixCount_conj {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
    fixCount H (x * g * x⁻¹) = fixCount H g := by
  unfold fixCount
  refine Nat.card_congr
    { toFun := fun y => ⟨x⁻¹ • y.1, ?_⟩
      invFun := fun y => ⟨x • y.1, ?_⟩
      left_inv := fun y => by simp
      right_inv := fun y => by simp }
  · have := y.2
    have h2 : (x * g * x⁻¹) • y.1 = y.1 := this
    calc g • x⁻¹ • y.1 = x⁻¹ • ((x * g * x⁻¹) • y.1) := by
          simp [mul_smul]
      _ = x⁻¹ • y.1 := by rw [h2]
  · have := y.2
    have h2 : g • y.1 = y.1 := this
    show (x * g * x⁻¹) • x • y.1 = x • y.1
    calc (x * g * x⁻¹) • x • y.1 = x • (g • y.1) := by simp [mul_smul]
      _ = x • y.1 := by rw [h2]

private lemma fixCount_pow {G : Type*} [Group G] [Finite G] (H : Subgroup G) (g : G) (k : ℕ)
    (hk : Nat.Coprime k (orderOf g)) : fixCount H (g ^ k) = fixCount H g := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hk
  unfold fixCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  constructor
  · intro h
    have h1 : g ^ k ∈ MulAction.stabilizer G x := h
    have h2 : (g ^ k) ^ m ∈ MulAction.stabilizer G x := Subgroup.pow_mem _ h1 m
    rw [hm] at h2
    exact h2
  · intro h
    have h1 : g ∈ MulAction.stabilizer G x := h
    exact (Subgroup.pow_mem _ h1 k : g ^ k ∈ MulAction.stabilizer G x)

private lemma fixCount_rat {G : Type*} [Group G] [Finite G] (H : Subgroup G) (g : G) (x : G)
    (k : ℕ) (hk : Nat.Coprime k (orderOf g)) : fixCount H (x * g ^ k * x⁻¹) = fixCount H g := by
  rw [fixCount_conj, fixCount_pow H g k hk]

private lemma exists_conj_mem_of_fixCount_ne {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (h : fixCount H g ≠ 0) : ∃ x : G, x⁻¹ * g * x ∈ H := by
  obtain ⟨⟨y, hy⟩, _⟩ := Nat.card_ne_zero.mp h
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hy' : (((g * x : G)) : G ⧸ H) = (x : G ⧸ H) := hy
    have h2 := H.inv_mem (QuotientGroup.eq.mp hy')
    exact ⟨x, by simpa [mul_assoc] using h2⟩

private lemma orderOf_conj' {G : Type*} [Group G] (x y : G) : orderOf (x * y * x⁻¹) = orderOf y := by
  have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective y
  simpa using this

private lemma fixCount_zpowers_key {G : Type*} [Group G] [Finite G] (g h : G)
    (hne : fixCount (Subgroup.zpowers g) h ≠ 0) :
    orderOf h ∣ orderOf g ∧ (orderOf h = orderOf g →
      ∃ (x : G) (k : ℕ), Nat.Coprime k (orderOf g) ∧ h = x * g ^ k * x⁻¹) := by
  obtain ⟨x, hx⟩ := exists_conj_mem_of_fixCount_ne _ _ hne
  have hx' : x⁻¹ * h * x ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr hx
  obtain ⟨j, hj⟩ := hx'
  have hh : h = x * g ^ j * x⁻¹ := by
    simp only at hj
    rw [hj]; group
  have ho : orderOf h = orderOf (g ^ j) := by rw [hh, orderOf_conj']
  refine ⟨?_, ?_⟩
  · rw [ho]; exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
  · intro h2
    refine ⟨x, j, ?_, hh⟩
    rw [ho, orderOf_pow] at h2
    have hpos : 0 < orderOf g := orderOf_pos g
    have : Nat.gcd (orderOf g) j = 1 := by
      have h3 : orderOf g / Nat.gcd (orderOf g) j * Nat.gcd (orderOf g) j = orderOf g :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      rw [h2] at h3
      have := Nat.eq_of_mul_eq_mul_left hpos (h3.trans (mul_one _).symm)
      exact this
    exact Nat.Coprime.symm this

private def IsRatFn {G : Type*} [Group G] (θ : G → ℝ) : Prop :=
  (∀ g x : G, θ (x * g * x⁻¹) = θ g) ∧
    (∀ (g : G) (k : ℕ), Nat.Coprime k (orderOf g) → θ (g ^ k) = θ g)

private lemma isRatFn_fix {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    IsRatFn (fun g : G => (fixCount H g : ℝ)) :=
  ⟨fun g x => by simp [fixCount_conj], fun g k hk => by simp [fixCount_pow H g k hk]⟩

private lemma fixCount_self_pos {G : Type*} [Group G] [Finite G] (g : G) :
    0 < (fixCount (Subgroup.zpowers g) g : ℝ) := by
  have : 0 < fixCount (Subgroup.zpowers g) g := by
    unfold fixCount
    have : Nonempty {x : G ⧸ Subgroup.zpowers g // g • x = x} :=
      ⟨⟨((1 : G) : G ⧸ Subgroup.zpowers g), by
        show (((g * 1 : G)) : G ⧸ Subgroup.zpowers g) = ((1 : G) : G ⧸ Subgroup.zpowers g)
        exact QuotientGroup.eq.mpr (by simp)⟩⟩
    exact Nat.card_pos
  exact_mod_cast this

private def spanW (G : Type*) [Group G] [Finite G] : Submodule ℝ (G → ℝ) :=
  Submodule.span ℝ (Set.range fun H : Subgroup G => fun g : G => (fixCount H g : ℝ))

private lemma main_span {G : Type*} [Group G] [Finite G] (n : ℕ) :
    ∀ θ : G → ℝ, IsRatFn θ → (∀ h, n < orderOf h → θ h = 0) → θ ∈ spanW G := by
  classical
  have := Fintype.ofFinite G
  induction n with
  | zero =>
    intro θ _ hθ
    have : θ = 0 := funext fun h => hθ h (orderOf_pos h)
    rw [this]; exact Submodule.zero_mem _
  | succ n ih =>
    have inner : ∀ m : ℕ, ∀ θ : G → ℝ, IsRatFn θ → (∀ h, n + 1 < orderOf h → θ h = 0) →
        (Finset.univ.filter fun h : G => orderOf h = n + 1 ∧ θ h ≠ 0).card = m → θ ∈ spanW G := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ihm =>
        intro θ hθ hvan hcard
        by_cases hempty : (Finset.univ.filter fun h : G => orderOf h = n + 1 ∧ θ h ≠ 0) = ∅
        · apply ih θ hθ
          intro h hh
          rcases Nat.lt_or_ge (n + 1) (orderOf h) with h1 | h1
          · exact hvan h h1
          · have h2 : orderOf h = n + 1 := by omega
            by_contra hne
            have : h ∈ (Finset.univ.filter fun h : G => orderOf h = n + 1 ∧ θ h ≠ 0) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨h2, hne⟩
            rw [hempty] at this
            simp at this
        · obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
          obtain ⟨hgo, hgθ⟩ := hg
          set φ : G → ℝ := fun h => (fixCount (Subgroup.zpowers g) h : ℝ) with hφ
          have hφpos : 0 < φ g := fixCount_self_pos g
          set a : ℝ := θ g / φ g with ha
          set θ' : G → ℝ := fun h => θ h - a * φ h with hθ'
          have hφrat := isRatFn_fix (Subgroup.zpowers g)
          have hθ'rat : IsRatFn θ' := by
            refine ⟨fun h x => ?_, fun h k hk => ?_⟩
            · simp only [hθ']
              rw [hθ.1 h x]
              have := hφrat.1 h x
              simp only [hφ] at this ⊢
              rw [this]
            · simp only [hθ']
              rw [hθ.2 h k hk]
              have := hφrat.2 h k hk
              simp only [hφ] at this ⊢
              rw [this]
          have hφvan : ∀ h, n + 1 < orderOf h → φ h = 0 := by
            intro h hh
            by_contra hne
            have : fixCount (Subgroup.zpowers g) h ≠ 0 := by
              intro h0; apply hne; simp [hφ, h0]
            have := Nat.le_of_dvd (orderOf_pos g) (fixCount_zpowers_key g h this).1
            omega
          have hθ'van : ∀ h, n + 1 < orderOf h → θ' h = 0 := by
            intro h hh
            simp only [hθ']
            rw [hvan h hh, hφvan h hh]; simp
          -- elements in the rational class of g
          have hcl : ∀ h, orderOf h = n + 1 → φ h ≠ 0 → θ' h = 0 := by
            intro h hh hne
            have hne' : fixCount (Subgroup.zpowers g) h ≠ 0 := by
              intro h0; apply hne; simp [hφ, h0]
            obtain ⟨x, k, hk, hhk⟩ := (fixCount_zpowers_key g h hne').2 (by omega)
            have e1 : θ h = θ g := by rw [hhk, hθ.1, hθ.2 g k hk]
            have e2 : φ h = φ g := by
              simp only [hφ]
              rw [hhk, fixCount_rat _ _ _ _ hk]
            simp only [hθ']
            rw [e1, e2, ha]
            field_simp
            ring
          have hsub : (Finset.univ.filter fun h : G => orderOf h = n + 1 ∧ θ' h ≠ 0) ⊂
              (Finset.univ.filter fun h : G => orderOf h = n + 1 ∧ θ h ≠ 0) := by
            refine ⟨?_, fun hsup => ?_⟩
            · intro h hh
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
              refine ⟨hh.1, fun h0 => hh.2 ?_⟩
              have : φ h = 0 := by
                by_contra hne
                exact hh.2 (hcl h hh.1 hne)
              simp only [hθ']
              rw [h0, this]; simp
            · have := hsup (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hgo, hgθ⟩)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
              exact this.2 (hcl g hgo hφpos.ne')
          have hlt := Finset.card_lt_card hsub
          have hmem := ihm _ (hcard ▸ hlt) θ' hθ'rat hθ'van rfl
          have hθeq : θ = θ' + a • φ := by
            funext h; simp [hθ']
          rw [hθeq]
          exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    exact fun θ hθ hvan => inner _ θ hθ hvan rfl

private lemma sum_fixCount {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    ∑ g : G, (fixCount H g : ℝ) = (Fintype.card G : ℝ) := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient G (G ⧸ H)) := Fintype.ofFinite _
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (G ⧸ H)
  have : Subsingleton (MulAction.orbitRel.Quotient G (G ⧸ H)) :=
    (MulAction.pretransitive_iff_subsingleton_quotient G (G ⧸ H)).mp inferInstance
  have : Nonempty (MulAction.orbitRel.Quotient G (G ⧸ H)) := ⟨Quotient.mk'' ((1 : G) : G ⧸ H)⟩
  have h1 : Fintype.card (MulAction.orbitRel.Quotient G (G ⧸ H)) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨Classical.arbitrary _, fun _ => Subsingleton.elim _ _⟩
  rw [h1, one_mul] at hb
  have : ∀ g : G, fixCount H g = Fintype.card (MulAction.fixedBy (G ⧸ H) g) := by
    intro g
    unfold fixCount
    rw [← Nat.card_eq_fintype_card]
    rfl
  simp_rw [this]
  exact_mod_cast hb

theorem solution {G : Type*} [Group G] [Fintype G] (θ : G → ℝ)
    (hconj : ∀ g x : G, θ (x * g * x⁻¹) = θ g)
    (hrat : ∀ (g : G) (k : ℕ), Nat.Coprime k (orderOf g) → θ (g ^ k) = θ g) :
    ∃ (S : Finset (Subgroup G)) (c : Subgroup G → ℝ),
      (∀ g : G, θ g = ∑ H ∈ S, c H * (fixCount H g : ℝ)) ∧
      ∑ H ∈ S, c H = (∑ g : G, θ g) / (Fintype.card G : ℝ) := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  have hmem : θ ∈ spanW G :=
    main_span (Fintype.card G) θ ⟨hconj, hrat⟩ (fun h hh => absurd (orderOf_le_card_univ (x := h)) (by omega))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hθ : ∀ g : G, θ g = ∑ H ∈ (Finset.univ : Finset (Subgroup G)), c H * (fixCount H g : ℝ) := by
    intro g
    rw [← hc]
    simp [Finset.sum_apply]
  refine ⟨Finset.univ, c, hθ, ?_⟩
  have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [eq_div_iff hpos.ne']
  calc (∑ H, c H) * (Fintype.card G : ℝ) = ∑ H, c H * (∑ g : G, (fixCount H g : ℝ)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun H _ => by rw [sum_fixCount]
    _ = ∑ g : G, ∑ H, c H * (fixCount H g : ℝ) := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    _ = ∑ g : G, θ g := Finset.sum_congr rfl fun g _ => (hθ g).symm
