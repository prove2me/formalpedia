-- Prove2me | solution 1 for CondPortOT.NullFiber.inf_mass_pos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T05:49:26.807518+00:00
-- url     : https://prove2.me/submissions/c8164c80-95ef-4144-a1f3-58e20cf57acd

import Mathlib
import Definitions.Def_CondPortOT_NullFiber_Setting

namespace NF43Aux
open MeasureTheory

/-- generic fiberwise sum lemma -/
theorem sum_div_card_le {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z] [DecidableEq Z]
    [MeasurableSingletonClass Z] {N : ℕ} (z : Fin N → Z) (ν : Measure (W × Z)) {A : Set W}
    (hA : MeasurableSet A) :
    ∑ i, ν (A ×ˢ {z i}) / ((Finset.univ.filter (fun j => z j = z i)).card : ENNReal) ≤
      ν (A ×ˢ Set.univ) := by
  let h : Z → ENNReal := fun w => ν (A ×ˢ {w}) / ((Finset.univ.filter (fun j => z j = w)).card : ENNReal)
  have e1 : ∑ i, ν (A ×ˢ {z i}) / ((Finset.univ.filter (fun j => z j = z i)).card : ENNReal)
      = ∑ i, h (z i) := rfl
  rw [e1, Finset.sum_comp]
  have e2 : ∀ w ∈ Finset.univ.image z,
      (Finset.univ.filter (fun j => z j = w)).card • h w = ν (A ×ˢ {w}) := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
    have hc : ((Finset.univ.filter (fun j => z j = z i)).card : ENNReal) ≠ 0 := by
      have : i ∈ Finset.univ.filter (fun j => z j = z i) := by simp
      exact_mod_cast (Finset.card_pos.2 ⟨i, this⟩).ne'
    simp only [h, nsmul_eq_mul]
    rw [ENNReal.mul_div_cancel hc (by simp)]
  rw [Finset.sum_congr rfl e2]
  rw [← measure_biUnion_finset]
  · apply measure_mono
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨w, -, hw⟩ := hp
    exact ⟨hw.1, trivial⟩
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_prod]
    right; simpa using hab
  · intro w _
    exact hA.prod (measurableSet_singleton w)

/-- the abstract knapsack value set -/
def KS {N : ℕ} (I : Finset (Fin N)) (d : Fin N → ℝ) (r q : ℝ) : Set (Fin N → ℝ) :=
  {p | (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (N : ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) ≤ r ∧
    (N : ℝ)⁻¹ * ∑ i ∈ I, p i ≤ q}

theorem KS_closed {N : ℕ} (I : Finset (Fin N)) (d : Fin N → ℝ) (r q : ℝ) :
    IsClosed (KS I d r q) := by
  have h1 : IsClosed {p : Fin N → ℝ | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} := by
    have : {p : Fin N → ℝ | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} = ⋂ i, (fun p : Fin N → ℝ => p i) ⁻¹' Set.Icc 0 1 := by
      ext p; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)
  have h2 : IsClosed {p : Fin N → ℝ | (N : ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) ≤ r} :=
    isClosed_le (by fun_prop) continuous_const
  have h3 : IsClosed {p : Fin N → ℝ | (N : ℝ)⁻¹ * ∑ i ∈ I, p i ≤ q} :=
    isClosed_le (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

theorem KS_compact {N : ℕ} (I : Finset (Fin N)) (d : Fin N → ℝ) (r q : ℝ) :
    IsCompact (KS I d r q) := by
  apply (isCompact_univ_pi (fun (_ : Fin N) => isCompact_Icc (a := (0:ℝ)) (b := 1))).of_isClosed_subset
    (KS_closed I d r q)
  intro p hp
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  exact hp.1

theorem KS_limit {N : ℕ} (I : Finset (Fin N)) (d : Fin N → ℝ) (ρ q : ℝ)
    (h : ∀ δ : ℝ, 0 < δ → (KS I d (ρ + δ) q).Nonempty) : (KS I d ρ q).Nonempty := by
  have hint := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => KS I d (ρ + 1 / ((n : ℝ) + 1)) q)
    (by
      intro n p hp
      refine ⟨hp.1, le_trans hp.2.1 ?_, hp.2.2⟩
      have : (1 : ℝ) / ((n + 1 : ℕ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast; linarith
      linarith)
    (fun n => h _ (by positivity)) (KS_compact _ _ _ _) (fun n => KS_closed _ _ _ _)
  obtain ⟨p, hp⟩ := hint
  simp only [Set.mem_iInter] at hp
  refine ⟨p, (hp 0).1, ?_, (hp 0).2.2⟩
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have := (hp n).2.1
  linarith

theorem KS_least_exists {N : ℕ} (I : Finset (Fin N)) (d : Fin N → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ εl : ℝ, IsLeast {r | ∃ p : Fin N → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧
      (N : ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) ≤ ρ ∧ r = (N : ℝ)⁻¹ * ∑ i ∈ I, p i} εl := by
  set S := {r | ∃ p : Fin N → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧
      (N : ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) ≤ ρ ∧ r = (N : ℝ)⁻¹ * ∑ i ∈ I, p i}
  have hS : S = (fun p : Fin N → ℝ => (N : ℝ)⁻¹ * ∑ i ∈ I, p i) ''
      {p | (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (N : ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) ≤ ρ} := by
    ext r; constructor
    · rintro ⟨p, h1, h2, rfl⟩; exact ⟨p, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨p, h1, h2, rfl⟩
  have hK : IsCompact {p : Fin N → ℝ | (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧
      (N : ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) ≤ ρ} := by
    apply (isCompact_univ_pi (fun (_ : Fin N) => isCompact_Icc (a := (0:ℝ)) (b := 1))).of_isClosed_subset
    · have h1 : IsClosed {p : Fin N → ℝ | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} := by
        have : {p : Fin N → ℝ | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} = ⋂ i, (fun p : Fin N → ℝ => p i) ⁻¹' Set.Icc 0 1 := by
          ext p; simp
        rw [this]
        exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)
      exact h1.inter (isClosed_le (f := fun p : Fin N → ℝ => (N : ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i)) (by fun_prop) continuous_const)
    · intro p hp
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      exact hp.1
  have hne : S.Nonempty := by
    refine ⟨(N : ℝ)⁻¹ * ∑ i ∈ I, (1 : ℝ), fun _ => 1, fun i => ⟨zero_le_one, le_refl _⟩, ?_, rfl⟩
    simp [hρ]
  rw [hS] at hne ⊢
  exact (hK.image (f := fun p : Fin N → ℝ => (N : ℝ)⁻¹ * ∑ i ∈ I, p i) (by fun_prop)).exists_isLeast hne

theorem coupling_bound {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ)
    (hA : CondPortOT.NullFiber.Assumption24 DX DY x0 γ xh)
    (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (Q : Measure (X × Y)) (π : Measure ((X × Y) × (X × Y))) [IsProbabilityMeasure π]
    (h1 : π.map Prod.fst = Q) (h2 : π.map Prod.snd = CondPortOT.SingUninf.empirical xh yh)
    (r : ℝ) (hc : ∫⁻ w, CondPortOT.SingUninf.groundCost DX DY w.1 w.2 ∂π < ENNReal.ofReal r) :
    (KS (CondPortOT.BigRadius.I1 DX x0 γ xh) (CondPortOT.BigRadius.bdDist DX x0 γ xh) r
      (Q (CondPortOT.SingUninf.fiber DX x0 γ)).toReal).Nonempty := by
  let _ : DecidableEq (X × Y) := Classical.decEq _
  set I := CondPortOT.BigRadius.I1 DX x0 γ xh
  set d := CondPortOT.BigRadius.bdDist DX x0 γ xh
  set F : Set (X × Y) := CondPortOT.SingUninf.fiber DX x0 γ with hFdef
  let z : Fin N → X × Y := fun i => (xh i, yh i)
  let m : Fin N → ℕ := fun i => (Finset.univ.filter (fun j => z j = z i)).card
  have hm1 : ∀ i, 1 ≤ m i := fun i => Finset.card_pos.2 ⟨i, by simp⟩
  have hFm : MeasurableSet F := by
    have : IsClosed (CondPortOT.SingUninf.nbhd DX x0 γ) :=
      isClosed_le (hA.cont_X.comp (continuous_id.prodMk continuous_const)) continuous_const
    exact this.measurableSet.prod MeasurableSet.univ
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hmass : ∀ i, π (Set.univ ×ˢ {z i}) = (N : ENNReal)⁻¹ * m i := by
    intro i
    rw [Set.univ_prod, ← Measure.map_apply measurable_snd (measurableSet_singleton _), h2]
    simp [CondPortOT.SingUninf.empirical, Measure.dirac_apply', Set.indicator_apply, m, z]
    congr 2
  have hsplit : ∀ i, π (F ×ˢ {z i}) + π (Fᶜ ×ˢ {z i}) = π (Set.univ ×ˢ {z i}) := by
    intro i
    rw [← measure_union _ ((hFm.compl).prod (measurableSet_singleton _))]
    · rw [← Set.union_prod, Set.union_compl_self]
    · rw [Set.disjoint_prod]; left; exact disjoint_compl_right
  let a : Fin N → ℝ := fun i => (π (F ×ˢ {z i})).toReal
  let b : Fin N → ℝ := fun i => (π (Fᶜ ×ˢ {z i})).toReal
  have hab : ∀ i, a i + b i = (m i : ℝ) / N := by
    intro i
    have := congrArg ENNReal.toReal ((hsplit i).trans (hmass i))
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    rw [this]; simp [div_eq_inv_mul]
  let p : Fin N → ℝ := fun i => (N : ℝ) * a i / m i
  have hmR : ∀ i, (0:ℝ) < m i := fun i => by exact_mod_cast hm1 i
  have ha0 : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
  have hb0 : ∀ i, 0 ≤ b i := fun i => ENNReal.toReal_nonneg
  have hNab : ∀ i, (N:ℝ) * (a i + b i) = m i := by
    intro i; rw [hab]; field_simp
  have hp1 : ∀ i, 1 - p i = (N:ℝ) * b i / m i := by
    intro i
    have := hNab i
    have hm := (hmR i).ne'
    simp only [p]
    field_simp
    linarith
  have hval : (N:ℝ)⁻¹ * ∑ i ∈ I, p i ≤ (Q F).toReal := by
    have e : (N:ℝ)⁻¹ * ∑ i ∈ I, p i = ∑ i ∈ I, a i / m i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [p]; field_simp
    rw [e]
    have hQF : Q F = π (F ×ˢ Set.univ) := by
      rw [← h1, Measure.map_apply measurable_fst hFm, Set.prod_univ]
    have key := sum_div_card_le z π hFm
    have e2 : ∑ i ∈ I, a i / m i = (∑ i ∈ I, π (F ×ˢ {z i}) / (m i : ENNReal)).toReal := by
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.toReal_div]; simp [a]
      · intro i _
        exact ENNReal.div_ne_top (measure_ne_top _ _) (by have := hm1 i; simp; omega)
    rw [e2, hQF]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ I)) key
  have hd0 : ∀ i ∈ I, 0 ≤ d i := fun i hi =>
    (hH2.exit_cost i hi).2 (by rintro _ ⟨x, -, rfl⟩; exact hA.nonneg_X _ _)
  have hdle : ∀ i ∈ I, ∀ x, x ∉ CondPortOT.SingUninf.nbhd DX x0 γ → d i ≤ DX x (xh i) :=
    fun i hi x hx => (hH2.exit_cost i hi).1 ⟨x, hx, rfl⟩
  let c : (X × Y) × (X × Y) → ENNReal := fun w => CondPortOT.SingUninf.groundCost DX DY w.1 w.2
  have hcm : Measurable c := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hx : Continuous fun w : (X × Y) × (X × Y) => DX w.1.1 w.2.1 :=
      hA.cont_X.comp (f := fun w : (X × Y) × (X × Y) => (w.1.1, w.2.1)) (by fun_prop)
    have hy : Continuous fun w : (X × Y) × (X × Y) => DY w.1.2 w.2.2 :=
      hA.cont_Y.comp (f := fun w : (X × Y) × (X × Y) => (w.1.2, w.2.2)) (by fun_prop)
    exact hx.add hy
  let ν := π.withDensity c
  have hT : ∀ i ∈ I, ENNReal.ofReal (d i) * π (Fᶜ ×ˢ {z i}) ≤ ν (Fᶜ ×ˢ {z i}) := by
    intro i hi
    have hS : MeasurableSet (Fᶜ ×ˢ {z i}) := hFm.compl.prod (measurableSet_singleton _)
    rw [withDensity_apply _ hS, ← setLIntegral_const]
    apply setLIntegral_mono' hS
    rintro ⟨w1, w2⟩ ⟨hw1, hw2⟩
    simp only [Set.mem_singleton_iff] at hw2
    subst hw2
    have hx : w1.1 ∉ CondPortOT.SingUninf.nbhd DX x0 γ := fun h => hw1 ⟨h, trivial⟩
    simp only [c, CondPortOT.SingUninf.groundCost, z]
    apply ENNReal.ofReal_le_ofReal
    have := hdle i hi _ hx
    have := hA.nonneg_Y w1.2 (yh i)
    linarith
  have hcost : (N:ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) ≤ r := by
    have e : (N:ℝ)⁻¹ * ∑ i ∈ I, d i * (1 - p i) = ∑ i ∈ I, d i * b i / m i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp1]; field_simp
    rw [e]
    have hsum : ∑ i ∈ I, ENNReal.ofReal (d i) * π (Fᶜ ×ˢ {z i}) / (m i : ENNReal) ≤ ∫⁻ w, c w ∂π := by
      calc _ ≤ ∑ i ∈ I, ν (Fᶜ ×ˢ {z i}) / (m i : ENNReal) :=
            Finset.sum_le_sum fun i hi => ENNReal.div_le_div_right (hT i hi) _
        _ ≤ ∑ i, ν (Fᶜ ×ˢ {z i}) / (m i : ENNReal) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ I)
        _ ≤ ν (Fᶜ ×ˢ Set.univ) := sum_div_card_le z ν hFm.compl
        _ ≤ ν Set.univ := measure_mono (Set.subset_univ _)
        _ = ∫⁻ w, c w ∂π := by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hlt := lt_of_le_of_lt hsum hc
    have e2 : ∑ i ∈ I, d i * b i / m i =
        (∑ i ∈ I, ENNReal.ofReal (d i) * π (Fᶜ ×ˢ {z i}) / (m i : ENNReal)).toReal := by
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hd0 i hi)]; simp [b]
      · intro i _
        exact ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (by have := hm1 i; simp; omega)
    rw [e2]
    exact (ENNReal.toReal_lt_of_lt_ofReal hlt).le
  refine ⟨p, fun i => ⟨by positivity, ?_⟩, hcost, hval⟩
  rw [div_le_one (hmR i)]
  nlinarith [hNab i, hb0 i]

theorem empirical_isProb {W : Type*} [MeasurableSpace W] {N : ℕ} (hN : 0 < N) (u : Fin N → W) :
    IsProbabilityMeasure ((N : ENNReal)⁻¹ • ∑ i, Measure.dirac (u i)) := by
  constructor
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp)

theorem empirical_map {W V : Type*} [MeasurableSpace W] [MeasurableSpace V] {N : ℕ}
    (u : Fin N → W) {f : W → V} (hf : Measurable f) :
    ((N : ENNReal)⁻¹ • ∑ i, Measure.dirac (u i)).map f = (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (f (u i)) := by
  ext s hs
  rw [Measure.map_apply hf hs]
  simp [Measure.dirac_apply' _ (hf hs), Measure.dirac_apply' _ hs]
  congr 1

theorem rhoMax_le {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ)
    (hA : CondPortOT.NullFiber.Assumption24 DX DY x0 γ xh)
    (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh) (ρ : ℝ)
    (hsum : (N : ℝ)⁻¹ * ∑ i ∈ CondPortOT.BigRadius.I1 DX x0 γ xh,
      CondPortOT.BigRadius.bdDist DX x0 γ xh i ≤ ρ) :
    CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ ≤ ENNReal.ofReal ρ := by
  classical
  set I := CondPortOT.BigRadius.I1 DX x0 γ xh with hIdef
  set d := CondPortOT.BigRadius.bdDist DX x0 γ xh
  set F : Set (X × Y) := CondPortOT.SingUninf.fiber DX x0 γ with hFdef
  have hFm : MeasurableSet F := by
    have : IsClosed (CondPortOT.SingUninf.nbhd DX x0 γ) :=
      isClosed_le (hA.cont_X.comp (continuous_id.prodMk continuous_const)) continuous_const
    exact this.measurableSet.prod MeasurableSet.univ
  have hd0 : ∀ i ∈ I, 0 ≤ d i := fun i hi =>
    (hH2.exit_cost i hi).2 (by rintro _ ⟨x, -, rfl⟩; exact hA.nonneg_X _ _)
  have hdiag : ∀ (x : X) (y : Y), DX x x = 0 ∧ DY y y = 0 := by
    intro x y
    have h := (hA.eq_zero_iff x x y y).2 rfl
    have := hA.nonneg_X x x; have := hA.nonneg_Y y y
    constructor <;> linarith
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεR : (0 : ℝ) < ε := hε
  have hx' : ∀ i, ∃ x', x' ∉ CondPortOT.SingUninf.nbhd DX x0 γ ∧
      DX x' (xh i) ≤ (if i ∈ I then d i else 0) + ε := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨_, ⟨x', hx', rfl⟩, -, hlt⟩ :=
        (hH2.exit_cost i hi).exists_between (lt_add_of_pos_right (d i) hεR)
      exact ⟨x', hx', by simp only [hi, if_true]; linarith⟩
    · refine ⟨xh i, ?_, ?_⟩
      · intro hmem; apply hi
        simp [hIdef, CondPortOT.BigRadius.I1, hmem]
      · simp only [hi, if_false, (hdiag (xh i) (yh i)).1]; linarith
  choose x' hx'n hx'c using hx'
  let Q' : Measure (X × Y) := (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (x' i, yh i)
  let π' : Measure ((X × Y) × (X × Y)) :=
    (N : ENNReal)⁻¹ • ∑ i, Measure.dirac ((x' i, yh i), (xh i, yh i))
  have hQ'prob : IsProbabilityMeasure Q' := empirical_isProb hN _
  have hπ'prob : IsProbabilityMeasure π' := empirical_isProb hN _
  have hQ'F : Q' F = 0 := by
    simp only [Q', Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.dirac_apply' _ hFm, smul_eq_mul]
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    rw [Set.indicator_of_notMem]
    exact fun h => hx'n i h.1
  have h1 : π'.map Prod.fst = Q' := empirical_map _ measurable_fst
  have h2 : π'.map Prod.snd = CondPortOT.SingUninf.empirical xh yh := empirical_map _ measurable_snd
  calc CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ
      ≤ RWPI.SqrtLasso.transportCost (CondPortOT.SingUninf.groundCost DX DY) Q'
          (CondPortOT.SingUninf.empirical xh yh) := iInf₂_le Q' ⟨hQ'prob, hQ'F⟩
    _ ≤ ∫⁻ w, CondPortOT.SingUninf.groundCost DX DY w.1 w.2 ∂π' := iInf₂_le π' ⟨hπ'prob, h1, h2⟩
    _ = (N : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (DX (x' i) (xh i) + DY (yh i) (yh i)) := by
        simp only [π', lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_dirac,
          smul_eq_mul, CondPortOT.SingUninf.groundCost]
    _ ≤ (N : ENNReal)⁻¹ * ENNReal.ofReal (∑ i ∈ I, d i + N * ε) := by
        gcongr
        have hnn : ∀ i ∈ Finset.univ, 0 ≤ (if i ∈ I then d i else 0) + (ε : ℝ) := by
          intro i _; split_ifs with hi
          · linarith [hd0 i hi]
          · linarith
        have e : ∑ i ∈ I, d i + N * (ε : ℝ) = ∑ i, ((if i ∈ I then d i else 0) + (ε : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]; simp
        rw [e, ENNReal.ofReal_sum_of_nonneg hnn]
        refine Finset.sum_le_sum fun i _ => ENNReal.ofReal_le_ofReal ?_
        rw [(hdiag (xh i) (yh i)).2, add_zero]
        exact hx'c i
    _ = ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i ∈ I, d i + ε) := by
        have hNR : (0 : ℝ) < N := by exact_mod_cast hN
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hNR,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal ρ + ε := by
        calc ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i ∈ I, d i + ε) ≤ ENNReal.ofReal (ρ + ε) :=
              ENNReal.ofReal_le_ofReal (by linarith)
          _ ≤ ENNReal.ofReal ρ + ENNReal.ofReal ε := ENNReal.ofReal_add_le
          _ = ENNReal.ofReal ρ + ε := by rw [ENNReal.ofReal_coe_nnreal]

theorem mass_lower {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ)
    (hA : CondPortOT.NullFiber.Assumption24 DX DY x0 γ xh)
    (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (εl : ℝ)
    (hεl : IsLeast (CondPortOT.NullFiber.knapsackSet DX x0 γ xh ρ) εl)
    (Q : Measure (X × Y)) (hQ : CondPortOT.SingUninf.InBall DX DY xh yh ρ Q) :
    ENNReal.ofReal εl ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ) := by
  obtain ⟨hQp, hT⟩ := hQ
  apply ENNReal.ofReal_le_of_le_toReal
  have hne : (KS (CondPortOT.BigRadius.I1 DX x0 γ xh) (CondPortOT.BigRadius.bdDist DX x0 γ xh) ρ
      (Q (CondPortOT.SingUninf.fiber DX x0 γ)).toReal).Nonempty := by
    apply KS_limit
    intro δ hδ
    have hlt : RWPI.SqrtLasso.transportCost (CondPortOT.SingUninf.groundCost DX DY) Q
        (CondPortOT.SingUninf.empirical xh yh) < ENNReal.ofReal (ρ + δ) :=
      lt_of_le_of_lt hT ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
    simp only [RWPI.SqrtLasso.transportCost, iInf_lt_iff] at hlt
    obtain ⟨π, ⟨hπp, h1, h2⟩, hc⟩ := hlt
    exact coupling_bound DX DY hN xh yh x0 γ hA hH2 Q π h1 h2 (ρ + δ) hc
  obtain ⟨p, hp1, hp2, hp3⟩ := hne
  exact le_trans (hεl.2 ⟨p, hp1, hp2, rfl⟩) hp3

theorem KS_zero {N : ℕ} (hN : 0 < N) (I : Finset (Fin N)) (d : Fin N → ℝ) (r : ℝ) (q : ℝ) (hq : q ≤ 0)
    (h : (KS I d r q).Nonempty) : (N : ℝ)⁻¹ * ∑ i ∈ I, d i ≤ r := by
  obtain ⟨p, hp1, hp2, hp3⟩ := h
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 ≤ ∑ i ∈ I, p i := Finset.sum_nonneg fun i _ => (hp1 i).1
  have hs : ∑ i ∈ I, p i = 0 := by
    have h2 := mul_nonneg (inv_nonneg.2 hNR.le) hs0
    have h3 : (N : ℝ)⁻¹ * ∑ i ∈ I, p i = 0 := le_antisymm (by linarith) h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (inv_ne_zero hNR.ne')
    · exact h
  have hp0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hp1 i).1)).1 hs
  convert hp2 using 2
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hp0 i hi]; ring

end NF43Aux

open MeasureTheory CondPortOT.NullFiber in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ)
    (hA : Assumption24 DX DY x0 γ xh) (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ < CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ) :
    0 < ⨅ (Q : Measure (X × Y)) (_ : CondPortOT.SingUninf.InBall DX DY xh yh ρ Q), Q (CondPortOT.SingUninf.fiber DX x0 γ) := by
  obtain ⟨εl, hεl⟩ := NF43Aux.KS_least_exists (CondPortOT.BigRadius.I1 DX x0 γ xh)
    (CondPortOT.BigRadius.bdDist DX x0 γ xh) ρ hρ0
  have hεl' : IsLeast (knapsackSet DX x0 γ xh ρ) εl := hεl
  have hpos : 0 < εl := by
    by_contra hle
    push_neg at hle
    obtain ⟨p, hp1, hp2, hp3⟩ := hεl'.1
    have hsum := NF43Aux.KS_zero hN (CondPortOT.BigRadius.I1 DX x0 γ xh)
      (CondPortOT.BigRadius.bdDist DX x0 γ xh) ρ εl hle ⟨p, hp1, hp2, hp3.ge⟩
    exact absurd (NF43Aux.rhoMax_le DX DY hN xh yh x0 γ hA hH2 ρ hsum) (not_le.2 hρ)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos)
    (le_iInf₂ fun Q hQ => NF43Aux.mass_lower DX DY hN xh yh x0 γ hA hH2 ρ hρ0 εl hεl' Q hQ)
