-- Prove2me | solution 1 for ChebotarevDensity.frobeniusCyclePattern_eq_factorDegrees
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:42:30.282289+00:00
-- url     : https://prove2.me/submissions/35fba5ea-2b5b-47e3-9732-a6c7b3dbd784

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

open ChebotarevDensity

private lemma sameCycle_iff_c {α β : Type*}
    (σ : Equiv.Perm α) (c : α → β) (h1 : ∀ x, c (σ x) = c x)
    (h2 : ∀ x y, c x = c y → σ.SameCycle x y) (x y : α) :
    σ.SameCycle x y ↔ c y = c x := by
  have hpow : ∀ k : ℤ, c ((σ ^ k) x) = c x := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [add_comm, zpow_one_add, Equiv.Perm.mul_apply, h1, ih]
    | pred i ih =>
      have : (σ ^ (-(i : ℤ) - 1)) x = σ⁻¹ ((σ ^ (-(i : ℤ))) x) := by
        rw [sub_eq_neg_add, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      rw [this, ← ih]
      have := h1 (σ⁻¹ ((σ ^ (-(i : ℤ))) x))
      simpa using this.symm
  constructor
  · rintro ⟨k, rfl⟩
    exact hpow k
  · intro h
    exact h2 x y h.symm

private lemma parts_eq_of_fibres {α β : Type*} [DecidableEq β] {_ : DecidableEq α}
    {_ : Fintype α}
    (σ : Equiv.Perm α) (c : α → β) (h1 : ∀ x, c (σ x) = c x)
    (h2 : ∀ x y, c x = c y → σ.SameCycle x y) :
    σ.partition.parts =
      (Finset.univ.image c).val.map (fun b => (Finset.univ.filter (fun x => c x = b)).card) := by
  set n : β → ℕ := fun b => (Finset.univ.filter (fun x => c x = b)).card with hn
  set B : Finset β := Finset.univ.image c with hB
  have hsc : ∀ x y, σ.SameCycle x y ↔ c y = c x := sameCycle_iff_c σ c h1 h2
  have hnpos : ∀ b ∈ B, 1 ≤ n b := by
    intro b hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.card_pos.mpr ⟨x, by simp⟩
  -- support of cycleOf
  have hsupp : ∀ x, σ x ≠ x → (σ.cycleOf x).support = Finset.univ.filter (fun y => c y = c x) := by
    intro x hx
    ext y
    rw [Equiv.Perm.mem_support_cycleOf_iff' hx, hsc]
    simp
  have hcard : ∀ x, σ x ≠ x → (σ.cycleOf x).support.card = n (c x) := by
    intro x hx
    rw [hsupp x hx]
  have hmovedl : ∀ x, 2 ≤ n (c x) → σ x ≠ x := by
    intro x hx hfix
    have : (Finset.univ.filter (fun y => c y = c x)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have e1 : σ.SameCycle x a := (hsc x a).mpr ha
      have e2 : σ.SameCycle x b := (hsc x b).mpr hb
      rw [← e1.eq_of_left hfix, ← e2.eq_of_left hfix]
    exact absurd hx (by simp only [n]; omega)
  set B₁ := B.filter (fun b => 2 ≤ n b) with hB₁
  set B₀ := B.filter (fun b => ¬ 2 ≤ n b) with hB₀
  have hsplit : B.val.map n = B₁.val.map n + B₀.val.map n := by
    rw [← Multiset.map_add]
    congr 1
    exact (Multiset.filter_add_not _ _).symm
  have hct : σ.cycleType = B₁.val.map n := by
    rw [Equiv.Perm.cycleType_def]
    have hex : ∀ b ∈ B₁.val, ∃ x, c x = b := by
      intro b hb
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (Finset.mem_val.mp hb)).1
      exact ⟨x, hx⟩
    symm
    refine Multiset.map_eq_map_of_bij_of_nodup n (Finset.card ∘ Equiv.Perm.support)
      B₁.nodup σ.cycleFactorsFinset.nodup
      (fun b hb => σ.cycleOf (Classical.choose (hex b hb))) ?_ ?_ ?_ ?_
    · intro b hb
      have hc := Classical.choose_spec (hex b hb)
      have h2b := (Finset.mem_filter.mp (Finset.mem_val.mp hb)).2
      rw [Finset.mem_val, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.mem_support]
      exact hmovedl _ (by rw [hc]; exact h2b)
    · intro a ha b hb hab
      have hca := Classical.choose_spec (hex a ha)
      have hcb := Classical.choose_spec (hex b hb)
      have ha2 := (Finset.mem_filter.mp (Finset.mem_val.mp ha)).2
      have hb2 := (Finset.mem_filter.mp (Finset.mem_val.mp hb)).2
      have hsa : Classical.choose (hex a ha) ∈ σ.support :=
        Equiv.Perm.mem_support.mpr (hmovedl _ (by rw [hca]; exact ha2))
      have hsb : Classical.choose (hex b hb) ∈ σ.support :=
        Equiv.Perm.mem_support.mpr (hmovedl _ (by rw [hcb]; exact hb2))
      have := (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hsa hsb).mpr hab
      have := (hsc _ _).mp this
      rw [hca, hcb] at this
      exact this.symm
    · intro z hz
      have hz' := Finset.mem_val.mp hz
      obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hz').1
      have hza := Equiv.Perm.cycle_is_cycleOf ha hz'
      have haσ : a ∈ σ.support := by
        rw [Equiv.Perm.mem_support]
        intro hfix
        have := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hz').2 a ha
        rw [Equiv.Perm.mem_support] at ha
        exact ha (by rw [this, hfix])
      have hmov : σ a ≠ a := Equiv.Perm.mem_support.mp haσ
      have hn2 : 2 ≤ n (c a) := by
        rw [← hcard a hmov, ← hza]
        exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hz').1.two_le_card_support
      have hbB₁ : c a ∈ B₁.val := by
        rw [Finset.mem_val, hB₁, Finset.mem_filter]
        exact ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, hn2⟩
      refine ⟨c a, hbB₁, ?_⟩
      have hc := Classical.choose_spec (hex (c a) hbB₁)
      have : σ.SameCycle a (Classical.choose (hex (c a) hbB₁)) := (hsc _ _).mpr hc
      rw [hza, this.cycleOf_eq]
    · intro b hb
      have hc := Classical.choose_spec (hex b hb)
      have h2b := (Finset.mem_filter.mp (Finset.mem_val.mp hb)).2
      have := hcard _ (hmovedl _ (by rw [hc]; exact h2b))
      rw [hc] at this
      simp only [Function.comp_apply]
      exact this.symm
  have hB₀1 : ∀ b ∈ B₀.val, n b = 1 := by
    intro b hb
    have hb' := Finset.mem_filter.mp (Finset.mem_val.mp hb)
    have := hnpos b hb'.1
    omega
  have hB₀map : B₀.val.map n = Multiset.replicate (Finset.card B₀) 1 := by
    rw [Multiset.map_congr rfl hB₀1, Multiset.map_const', Finset.card_val]
  have hsum_all : Fintype.card α = ∑ b ∈ B, n b := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_image c Finset.univ]
  have hsum₁ : (Finset.card σ.support) = ∑ b ∈ B₁, n b := by
    rw [← Equiv.Perm.sum_cycleType, hct]
    rfl
  have hsum₀ : ∑ b ∈ B₀, n b = Finset.card B₀ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl (fun b hb => hB₀1 b hb)
  have hsplit' : ∑ b ∈ B, n b = ∑ b ∈ B₁, n b + ∑ b ∈ B₀, n b :=
    (Finset.sum_filter_add_sum_filter_not B (fun b => 2 ≤ n b) n).symm
  rw [Equiv.Perm.parts_partition, hct, hsplit, hB₀map]
  congr 2
  omega

private lemma frob_action (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X])
    [Fact (g.map (algebraMap (ZMod p) g.SplittingField)).Splits]
    (x : g.rootSet g.SplittingField) :
    ((Polynomial.Gal.galActionHom g g.SplittingField
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) g.SplittingField) x :
        g.rootSet g.SplittingField) : g.SplittingField) = (x : g.SplittingField) ^ p := by
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) g.SplittingField with hφ
  have hr : Polynomial.Gal.restrict g g.SplittingField φ = φ := by
    refine AlgEquiv.ext fun y => ?_
    let _ : Algebra g.SplittingField g.SplittingField :=
      (IsSplittingField.lift g.SplittingField g (Fact.out)).toRingHom.toAlgebra
    apply (algebraMap g.SplittingField g.SplittingField).injective
    have := AlgEquiv.restrictNormal_commutes φ g.SplittingField y
    refine this.trans ?_
    simp only [hφ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card, map_pow]
  have h3 := Polynomial.Gal.galActionHom_restrict g g.SplittingField φ x
  rw [hr] at h3
  simpa [hφ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using h3

private lemma core (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X]) (hg : Squarefree g)
    {_ : DecidableEq (g.rootSet g.SplittingField)} {_ : Fintype (g.rootSet g.SplittingField)}
    (σ : Equiv.Perm (g.rootSet g.SplittingField))
    (hσ : ∀ x, ((σ x : g.rootSet g.SplittingField) : g.SplittingField) =
      (x : g.SplittingField) ^ p) :
    σ.partition.parts = (UniqueFactorizationMonoid.normalizedFactors g).map natDegree := by
  classical
  have hg0 : g ≠ 0 := fun h => by simp [h] at hg
  set L := g.SplittingField with hL
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L with hφ
  have hφx : ∀ y : L, φ y = y ^ p := by
    intro y
    simp [hφ, ZMod.card]
  have hσφ : ∀ x, ((σ x : g.rootSet L) : L) = φ x := fun x => by rw [hσ, hφx]
  have hσφn : ∀ (n : ℕ) x, (((σ ^ n) x : g.rootSet L) : L) = (φ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, AlgEquiv.mul_apply, ih, hσφ]
  set c : g.rootSet L → (ZMod p)[X] := fun x => minpoly (ZMod p) (x : L) with hc
  have h1 : ∀ x, c (σ x) = c x := by
    intro x
    simp only [hc]
    rw [hσφ, minpoly.algEquiv_eq]
  have h2 : ∀ x y, c x = c y → σ.SameCycle x y := by
    intro x y hxy
    obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ZMod p) (E := L)).mp hxy
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) L).2 τ
    have hτ' : τ y = x := hτ
    refine Equiv.Perm.SameCycle.symm (show σ.SameCycle y x from ⟨(n.1 : ℤ), ?_⟩)
    apply Subtype.ext
    rw [zpow_natCast, hσφn]
    simp only at hn
    rw [hn, hτ']
  rw [parts_eq_of_fibres σ c h1 h2]
  have hnd : (UniqueFactorizationMonoid.normalizedFactors g).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hg0).mp hg
  have key : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors g,
      Irreducible b ∧ b.Monic ∧ b ∣ g := by
    intro b hb
    refine ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb, ?_,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb⟩
    have h := UniqueFactorizationMonoid.normalize_normalized_factor b hb
    have hb0 : b ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb).ne_zero
    rw [← h]
    exact Polynomial.monic_normalize hb0
  have hg_root : ∀ y : L, aeval y g = 0 → y ∈ g.rootSet L := fun y hy =>
    (mem_rootSet_of_ne hg0).mpr hy
  have hmem : ∀ b, b ∈ Finset.univ.image c ↔
      b ∈ UniqueFactorizationMonoid.normalizedFactors g := by
    intro b
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, -, rfl⟩
      have hx : aeval (x : L) g = 0 := (mem_rootSet_of_ne hg0).mp x.2
      have hint : IsIntegral (ZMod p) (x : L) := Algebra.IsIntegral.isIntegral _
      have hd : minpoly (ZMod p) (x : L) ∣ g := minpoly.dvd _ _ hx
      obtain ⟨q, hq, hassoc⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hg0
        (minpoly.irreducible hint) hd
      have : minpoly (ZMod p) (x : L) = q :=
        Polynomial.eq_of_monic_of_associated (minpoly.monic hint) (key q hq).2.1 hassoc
      show minpoly (ZMod p) (x : L) ∈ _
      rw [this]; exact hq
    · intro hb
      obtain ⟨hirr, hmon, hdvd⟩ := key b hb
      have hsplit : Splits (b.map (algebraMap (ZMod p) L)) := by
        have h0 : g.map (algebraMap (ZMod p) L) ≠ 0 :=
          (Polynomial.map_ne_zero_iff (algebraMap (ZMod p) L).injective).mpr hg0
        exact (SplittingField.splits g).of_dvd h0 (Polynomial.map_dvd _ hdvd)
      obtain ⟨y, hy⟩ := Splits.exists_eval_eq_zero hsplit (by
        rw [degree_map]
        exact (Polynomial.degree_pos_of_irreducible hirr).ne')
      have hy' : aeval y b = 0 := by
        rw [aeval_def, eval₂_eq_eval_map]; exact hy
      have hyg : aeval y g = 0 := by
        obtain ⟨h, rfl⟩ := hdvd
        simp [hy']
      refine ⟨⟨y, hg_root y hyg⟩, Finset.mem_univ _, ?_⟩
      exact (minpoly.eq_of_irreducible_of_monic hirr hy' hmon).symm
  have hfib : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors g,
      (Finset.univ.filter (fun x => c x = b)).card = b.natDegree := by
    intro b hb
    obtain ⟨hirr, hmon, hdvd⟩ := key b hb
    have hsplit : Splits (b.map (algebraMap (ZMod p) L)) := by
      have h0 : g.map (algebraMap (ZMod p) L) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (algebraMap (ZMod p) L).injective).mpr hg0
      exact (SplittingField.splits g).of_dvd h0 (Polynomial.map_dvd _ hdvd)
    rw [← card_rootSet_eq_natDegree (K := L) (PerfectField.separable_of_irreducible hirr) hsplit]
    rw [← Fintype.card_subtype]
    have hA : ∀ x : {x : g.rootSet L // c x = b}, ((x.1 : g.rootSet L) : L) ∈ b.rootSet L := by
      intro x
      have hxb : minpoly (ZMod p) ((x.1 : g.rootSet L) : L) = b := x.2
      rw [mem_rootSet_of_ne hirr.ne_zero]
      have := minpoly.aeval (ZMod p) ((x.1 : g.rootSet L) : L)
      rwa [hxb] at this
    have hB : ∀ y : b.rootSet L, (y : L) ∈ g.rootSet L := by
      intro y
      have hy : aeval (y : L) b = 0 := (mem_rootSet_of_ne hirr.ne_zero).mp y.2
      apply hg_root
      obtain ⟨h, rfl⟩ := hdvd
      simp [hy]
    have hC : ∀ y : b.rootSet L, c ⟨y.1, hB y⟩ = b := by
      intro y
      have hy : aeval (y : L) b = 0 := (mem_rootSet_of_ne hirr.ne_zero).mp y.2
      exact (minpoly.eq_of_irreducible_of_monic hirr hy hmon).symm
    exact Fintype.card_congr
      { toFun := fun x => ⟨(x.1 : L), hA x⟩
        invFun := fun y => ⟨⟨y.1, hB y⟩, hC y⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have himg : Finset.univ.image c = (UniqueFactorizationMonoid.normalizedFactors g).toFinset :=
    Finset.ext fun b => by rw [hmem, Multiset.mem_toFinset]
  rw [himg, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  exact Multiset.map_congr rfl hfib

theorem solution (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X])
    (hg : Squarefree g) :
    frobeniusCyclePattern p g =
      (UniqueFactorizationMonoid.normalizedFactors g).map natDegree := by
  unfold frobeniusCyclePattern
  have : Fact (g.map (algebraMap (ZMod p) g.SplittingField)).Splits :=
    ⟨SplittingField.splits g⟩
  exact core p g hg _ (fun x => frob_action p g x)
