-- Prove2me | solution 2 for CondRiskMap.Repr.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T23:03:22.900451+00:00
-- url     : https://prove2.me/submissions/9e9016d7-deaf-4bbe-a023-05a0c9e05dd8

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

set_option autoImplicit false

namespace CondRiskMap.Repr.T2Aux

open MeasureTheory CondRiskMap.Repr

section Meas
variable {Ω : Type*} [MeasurableSpace Ω]

lemma pair_indicator (μ : SignedMeasure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    pair μ (A.indicator 1) = μ A := by
  unfold pair
  rw [integral_indicator_one hA, integral_indicator_one hA,
    μ.apply_eq_posPart_real_sub_negPart_real hA]

lemma negPart_eq_zero {μ : SignedMeasure Ω} (h : 0 ≤ μ) :
    μ.toJordanDecomposition.negPart = 0 := by
  obtain ⟨N, hN, hP, hQ⟩ := μ.toJordanDecomposition.mutuallySingular
  have h1 := μ.apply_eq_posPart_real_sub_negPart_real hN
  have h2 : 0 ≤ μ N := by
    have := (VectorMeasure.le_iff.1 h) N hN
    simpa using this
  have h3 : μ.toJordanDecomposition.posPart.real N = 0 := by
    simp [Measure.real, hP]
  have h4 : μ.toJordanDecomposition.negPart N = 0 := by
    have h5 : μ.toJordanDecomposition.negPart.real N = 0 := by
      have := measureReal_nonneg (μ := μ.toJordanDecomposition.negPart) (s := N)
      linarith
    rwa [measureReal_eq_zero_iff] at h5
  apply Measure.measure_univ_eq_zero.1
  rw [← Set.union_compl_self N]
  exact measure_union_null h4 hQ

lemma apply_eq_posPart {μ : SignedMeasure Ω} (h0 : 0 ≤ μ) {s : Set Ω} (hs : MeasurableSet s) :
    μ s = μ.toJordanDecomposition.posPart.real s := by
  rw [μ.apply_eq_posPart_real_sub_negPart_real hs, negPart_eq_zero h0]
  simp

lemma posPart_null {μ : SignedMeasure Ω} (h0 : 0 ≤ μ) {s : Set Ω} (hs : MeasurableSet s)
    (h : μ s = 0) : μ.toJordanDecomposition.posPart s = 0 := by
  rw [apply_eq_posPart h0 hs, measureReal_eq_zero_iff] at h
  exact h

lemma pair_eq_of_const {μ : SignedMeasure Ω} (h0 : 0 ≤ μ) (h1 : μ Set.univ = 1)
    {E : Set Ω} (hE : MeasurableSet E) (hμE : μ E = 1) (g : Ω → ℝ) (c : ℝ)
    (hg : ∀ ω ∈ E, g ω = c) : pair μ g = c := by
  unfold pair
  rw [negPart_eq_zero h0, integral_zero_measure, sub_zero]
  have hPu : μ.toJordanDecomposition.posPart.real Set.univ = 1 := by
    rw [← apply_eq_posPart h0 MeasurableSet.univ, h1]
  have hEc : μ Eᶜ = 0 := by
    have := μ.of_union (disjoint_compl_right (a := E)) hE hE.compl
    rw [Set.union_compl_self, h1, hμE] at this
    linarith
  have hPc := posPart_null h0 hE.compl hEc
  have hae : g =ᵐ[μ.toJordanDecomposition.posPart] fun _ => c := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hPc
    by_contra hc
    exact hω (hg ω (by simpa using hc))
  rw [integral_congr_ae hae, integral_const, smul_eq_mul, hPu, one_mul]

end Meas

section Main
variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
  [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
  [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]

/-- The measures `μ ∈ 𝒫_{𝒴₂|ℱ₁}(ω)` with `⟨μ, ·⟩ ≤ ρ_ω`. -/
def Good (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (ω : Ω) : Set 𝒴 :=
  {μ | μ ∈ ProbGiven S ω ∧ ∀ X, pair (S.toMeasure μ) (S.toFun X) ≤ ρω S ρ ω X}

lemma rho_zero {ρ : 𝒳 → 𝒳} (hph : PosHomogeneous ρ) : ρ 0 = 0 := by
  have := hph 2 0 two_pos
  rw [smul_zero, two_smul] at this
  simpa using this

lemma exists_good [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (hC : CondC S) (hC' : CondC' S)
    (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ)
    (ω : Ω) (X₀ : 𝒳) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ ∈ Good S ρ ω, ρω S ρ ω X₀ - ε < pair (S.toMeasure μ) (S.toFun X₀) := by
  obtain ⟨hmaps, hA1, hA2, hA3⟩ := hρ
  set f := ρω S ρ ω with hf
  have f0 : f 0 = 0 := by
    simp only [hf, ρω, rho_zero hph, map_zero, Pi.zero_apply]
  have fhom : ∀ t : ℝ, 0 < t → ∀ X, f (t • X) = t * f X := by
    intro t ht X
    simp only [hf, ρω, hph t X ht, map_smul, Pi.smul_apply, smul_eq_mul]
  set T : Set (𝒳 × ℝ) := {p | f p.1 ≤ p.2} with hT
  have hTc : IsClosed T := (hlsc ω).isClosed_epigraph
  have hTconv : Convex ℝ T := by
    intro p hp q hq a b ha hb hab
    simp only [hT, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at *
    have hb' : b = 1 - a := by linarith
    subst hb'
    calc f (a • p.1 + (1 - a) • q.1) ≤ a * f p.1 + (1 - a) * f q.1 :=
          hA1 a ha (by linarith) _ _ ω
      _ ≤ a * p.2 + (1 - a) * q.2 := by
          have := mul_le_mul_of_nonneg_left hp ha
          have := mul_le_mul_of_nonneg_left hq hb
          linarith
  have hnot : (X₀, f X₀ - ε) ∉ T := by
    simp only [hT, Set.mem_setOf_eq, not_le]
    linarith
  obtain ⟨φ, u, hφx, hφT⟩ := geometric_hahn_banach_point_closed hTconv hTc hnot
  set g : 𝒳 →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ 𝒳 ℝ) with hg
  set c : ℝ := φ ((0 : 𝒳), (1 : ℝ)) with hc
  have hφ : ∀ X t, φ (X, t) = g X + t * c := by
    intro X t
    have : ((X, t) : 𝒳 × ℝ) = (X, (0 : ℝ)) + t • ((0 : 𝒳), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have hu0 : u < 0 := by
    have := hφT (0, 0) (by simp [hT, f0])
    simpa [Prod.mk_zero_zero] using this
  have hpos : ∀ X, 0 ≤ g X + c * f X := by
    intro X
    by_contra hneg
    push_neg at hneg
    set δ := -(g X + c * f X) with hδdef
    have hδ : 0 < δ := by linarith
    set s := -u / δ + 1 with hsdef
    have hs0 : 0 < -u / δ := div_pos (by linarith) hδ
    have hs : 0 < s := by linarith
    have hmem : (s • X, f (s • X)) ∈ T := by simp [hT]
    have h1 := hφT _ hmem
    rw [hφ, fhom s hs X, map_smul, smul_eq_mul] at h1
    have h2 : s * g X + s * f X * c = -(s * δ) := by rw [hδdef]; ring
    have h3 : s * δ = -u + δ := by
      rw [hsdef, add_mul, div_mul_cancel₀ _ hδ.ne', one_mul]
    linarith
  have hcpos : 0 < c := by
    have h1 := hφx
    rw [hφ] at h1
    have h2 := hpos X₀
    by_contra hcn
    push_neg at hcn
    nlinarith
  set ℓ : 𝒳 →L[ℝ] ℝ := (-(1 / c)) • g with hℓdef
  obtain ⟨μ, hμ⟩ := S.dual_rep_X ℓ
  have hℓ : ∀ X, ℓ X = -(g X) / c := by
    intro X
    simp only [hℓdef, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hle : ∀ X, pair (S.toMeasure μ) (S.toFun X) ≤ f X := by
    intro X
    rw [← hμ, hℓ, div_le_iff₀ hcpos]
    have := hpos X
    linarith
  have hval : ∀ B, MeasurableSet[S.F₁] B → S.toMeasure μ B = B.indicator 1 ω := by
    intro B hB
    obtain ⟨Y, hY, hYf⟩ := hC' B hB
    have hρY : ∀ t : ℝ, ρ (t • Y) = t • Y := by
      intro t
      have := hA3 (t • Y) (S.X₁.smul_mem t hY) 0
      rwa [zero_add, rho_zero hph, zero_add] at this
    have hfY : ∀ t : ℝ, f (t • Y) = t * B.indicator 1 ω := by
      intro t
      simp only [hf, ρω, hρY t, map_smul, Pi.smul_apply, smul_eq_mul, hYf]
    have hpY : pair (S.toMeasure μ) (S.toFun Y) = S.toMeasure μ B := by
      rw [hYf]
      exact pair_indicator _ (S.F₁_le B hB)
    have hl1 := hle ((1 : ℝ) • Y)
    have hl2 := hle ((-1 : ℝ) • Y)
    rw [← hμ, map_smul, smul_eq_mul, hμ, hpY, hfY] at hl1 hl2
    linarith
  refine ⟨μ, ⟨⟨⟨?_, ?_⟩, hval⟩, hle⟩, ?_⟩
  · by_contra hn
    obtain ⟨X, hX0, hXneg⟩ := hC μ hn
    have h1 := hle (-X)
    rw [← hμ, map_neg, hμ] at h1
    have h2 : f (-X) ≤ f 0 := hA2 (-X) 0 (fun ω' => by simp [hX0 ω']) ω
    linarith
  · have := hval Set.univ MeasurableSet.univ
    simpa using this
  · rw [← hμ, hℓ, lt_div_iff₀ hcpos]
    have h1 := hφx
    rw [hφ] at h1
    linarith

/-- The `ℱ₁`-atom of `ω`. -/
def atom (S : PairedSpaces Ω 𝒳 𝒴) (ω : Ω) : Set Ω :=
  {ω' | ∀ B, MeasurableSet[S.F₁] B → (ω' ∈ B ↔ ω ∈ B)}

lemma mem_atom_self (S : PairedSpaces Ω 𝒳 𝒴) (ω : Ω) : ω ∈ atom S ω := fun _ _ => Iff.rfl

lemma atom_eq_of_mem (S : PairedSpaces Ω 𝒳 𝒴) {ω ω' : Ω} (h : ω' ∈ atom S ω) :
    atom S ω' = atom S ω := by
  ext x
  simp only [atom, Set.mem_setOf_eq]
  constructor
  · intro hx B hB
    rw [hx B hB, h B hB]
  · intro hx B hB
    rw [hx B hB, h B hB]

lemma rhoω_eq_of_mem (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (hm : MapsToX₁ S ρ)
    {ω ω' : Ω} (h : ω' ∈ atom S ω) (X : 𝒳) : ρω S ρ ω' X = ρω S ρ ω X := by
  have hmeas := S.X₁_measurable _ (hm X)
  have hB : MeasurableSet[S.F₁] (S.toFun (ρ X) ⁻¹' {S.toFun (ρ X) ω}) :=
    hmeas (measurableSet_singleton _)
  have := (h _ hB).2 rfl
  exact this

lemma Good_eq_of_mem (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (hm : MapsToX₁ S ρ)
    {ω ω' : Ω} (h : ω' ∈ atom S ω) : Good S ρ ω' = Good S ρ ω := by
  ext μ
  simp only [Good, ProbGiven, Set.mem_setOf_eq, rhoω_eq_of_mem S ρ hm h]
  have hind : ∀ B, MeasurableSet[S.F₁] B → B.indicator (1 : Ω → ℝ) ω' = B.indicator 1 ω := by
    intro B hB
    by_cases hω : ω ∈ B
    · simp [Set.indicator_of_mem hω, Set.indicator_of_mem ((h B hB).2 hω)]
    · rw [Set.indicator_of_notMem hω,
        Set.indicator_of_notMem (fun h' => hω ((h B hB).1 h'))]
  constructor
  · rintro ⟨⟨hP, hB⟩, hle⟩
    exact ⟨⟨hP, fun B hB' => (hB B hB').trans (hind B hB')⟩, hle⟩
  · rintro ⟨⟨hP, hB⟩, hle⟩
    exact ⟨⟨hP, fun B hB' => (hB B hB').trans (hind B hB').symm⟩, hle⟩

lemma atoms_finite (S : PairedSpaces Ω 𝒳 𝒴) (hI : HasIndicators S) (hPc : IsCompact (Prob S))
    (hne : ∀ ω, ∃ μ, μ ∈ ProbGiven S ω) : (Set.range (atom S)).Finite := by
  by_contra hinf
  have emb := (Set.not_finite.1 hinf).natEmbedding
  have hw : ∀ n, ∃ w, atom S w = (emb n : Set Ω) := fun n => (emb n).2
  choose w hw using hw
  have hsep : ∀ n m, ∃ B, MeasurableSet[S.F₁] B ∧ w n ∈ B ∧ (n ≠ m → w m ∉ B) := by
    intro n m
    by_cases hnm : n = m
    · exact ⟨Set.univ, MeasurableSet.univ, Set.mem_univ _, fun h => (h hnm).elim⟩
    · have hne' : atom S (w n) ≠ atom S (w m) := by
        rw [hw, hw]
        intro h
        exact hnm (emb.injective (Subtype.ext h))
      have hnot : w m ∉ atom S (w n) := fun h => hne' (atom_eq_of_mem S h).symm
      simp only [atom, Set.mem_setOf_eq, not_forall] at hnot
      obtain ⟨B, hB, hiff⟩ := hnot
      by_cases hwn : w n ∈ B
      · exact ⟨B, hB, hwn, fun _ hwm => hiff ⟨fun _ => hwn, fun _ => hwm⟩⟩
      · refine ⟨Bᶜ, hB.compl, hwn, fun _ hwm => hiff ⟨fun h => (hwm h).elim, fun h => (hwn h).elim⟩⟩
  choose Bs hBs using hsep
  let C : ℕ → Set Ω := fun n => ⋂ m, Bs n m
  have hCm : ∀ n, MeasurableSet[S.F₁] (C n) := fun n => MeasurableSet.iInter fun m => (hBs n m).1
  have hCw : ∀ n, w n ∈ C n := fun n => Set.mem_iInter.2 fun m => (hBs n m).2.1
  have hCw' : ∀ n m, n ≠ m → w m ∉ C n := fun n m h hm => (hBs n m).2.2 h (Set.mem_iInter.1 hm m)
  let E : Set Ω := ⋃ n, C n
  have hEm : MeasurableSet[S.F₁] E := MeasurableSet.iUnion hCm
  choose μ hμ using fun n => hne (w n)
  obtain ⟨XE, hXE⟩ := hI E (S.F₁_le _ hEm)
  choose XC hXC using fun k => hI (C k) (S.F₁_le _ (hCm k))
  let K : Set 𝒴 := Prob S ∩ {ν | pair (S.toMeasure ν) (S.toFun XE) = 1}
  have hKc : IsCompact K := hPc.inter_right (isClosed_eq (S.continuous_pair_Y XE) continuous_const)
  let V : ℕ → Set 𝒴 := fun k => {ν | 0 < pair (S.toMeasure ν) (S.toFun (XC k))}
  have hVo : ∀ k, IsOpen (V k) := fun k => isOpen_lt continuous_const (S.continuous_pair_Y _)
  have hcov : K ⊆ ⋃ k, V k := by
    rintro ν ⟨⟨h0, h1⟩, hE1⟩
    rw [Set.mem_iUnion]
    by_contra hall
    push_neg at hall
    have hz : ∀ k, (S.toMeasure ν).toJordanDecomposition.posPart (C k) = 0 := by
      intro k
      have hk := hall k
      simp only [V, Set.mem_setOf_eq, not_lt, hXC k, pair_indicator _ (S.F₁_le _ (hCm k))] at hk
      have hk0 := (VectorMeasure.le_iff.1 h0) (C k) (S.F₁_le _ (hCm k))
      simp only [VectorMeasure.zero_apply] at hk0
      exact posPart_null h0 (S.F₁_le _ (hCm k)) (le_antisymm hk hk0)
    have hEz := measure_iUnion_null hz
    have hE1' : pair (S.toMeasure ν) (S.toFun XE) = 1 := hE1
    simp only [hXE, pair_indicator _ (S.F₁_le _ hEm)] at hE1'
    rw [apply_eq_posPart h0 (S.F₁_le _ hEm)] at hE1'
    simp [Measure.real, E, hEz] at hE1'
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover V hVo hcov
  set M := t.sup id + 1 with hM
  have hμK : μ M ∈ K := by
    refine ⟨(hμ M).1, ?_⟩
    simp only [Set.mem_setOf_eq, hXE, pair_indicator _ (S.F₁_le _ hEm), (hμ M).2 E hEm]
    rw [Set.indicator_of_mem (Set.mem_iUnion.2 ⟨M, hCw M⟩)]
    rfl
  have := ht hμK
  simp only [Set.mem_iUnion] at this
  obtain ⟨i, hi, hV⟩ := this
  have hiM : i ≠ M := by
    have : i ≤ t.sup id := Finset.le_sup (f := id) hi
    omega
  simp only [V, Set.mem_setOf_eq, hXC i, pair_indicator _ (S.F₁_le _ (hCm i)),
    (hμ M).2 _ (hCm i), Set.indicator_of_notMem (hCw' i M hiM)] at hV
  exact lt_irrefl _ hV

lemma atom_measurable (S : PairedSpaces Ω 𝒳 𝒴) (hfin : (Set.range (atom S)).Finite) (ω : Ω) :
    MeasurableSet[S.F₁] (atom S ω) := by
  classical
  let T : Set Ω → Set Ω := fun a =>
    if h : ∃ B, MeasurableSet[S.F₁] B ∧ ω ∈ B ∧ Disjoint a B then h.choose else Set.univ
  have hTm : ∀ a, MeasurableSet[S.F₁] (T a) := by
    intro a
    simp only [T]
    split_ifs with h
    · exact h.choose_spec.1
    · exact MeasurableSet.univ
  have heq : atom S ω = ⋂ a ∈ Set.range (atom S), T a := by
    ext x
    simp only [Set.mem_iInter]
    constructor
    · intro hx a _
      simp only [T]
      split_ifs with h
      · exact (hx _ h.choose_spec.1).2 h.choose_spec.2.1
      · exact Set.mem_univ _
    · intro hx
      by_contra hxn
      simp only [atom, Set.mem_setOf_eq, not_forall] at hxn
      obtain ⟨B, hB, hiff⟩ := hxn
      have hex : ∃ B, MeasurableSet[S.F₁] B ∧ ω ∈ B ∧ Disjoint (atom S x) B := by
        by_cases hωB : ω ∈ B
        · have hxB : x ∉ B := fun h => hiff ⟨fun _ => hωB, fun _ => h⟩
          refine ⟨B, hB, hωB, Set.disjoint_left.2 fun y hy hyB => hxB ((hy B hB).1 hyB)⟩
        · have hxB : x ∈ B := by
            by_contra h
            exact hiff ⟨fun h' => (h h').elim, fun h' => (hωB h').elim⟩
          refine ⟨Bᶜ, hB.compl, hωB, Set.disjoint_left.2 fun y hy hyB => hyB ((hy B hB).2 hxB)⟩
      have hxT := hx (atom S x) ⟨x, rfl⟩
      simp only [T, dif_pos hex] at hxT
      exact Set.disjoint_left.1 hex.choose_spec.2.2 (mem_atom_self S x) hxT
  rw [heq]
  exact MeasurableSet.biInter hfin.countable fun a _ => hTm a

lemma atom_fun_measurable (S : PairedSpaces Ω 𝒳 𝒴) (hfin : (Set.range (atom S)).Finite)
    (h : Set Ω → ℝ) : Measurable[S.F₁] fun ω => h (atom S ω) := by
  intro U _
  have heq : (fun ω => h (atom S ω)) ⁻¹' U = ⋃ a ∈ {a | a ∈ Set.range (atom S) ∧ h a ∈ U}, a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      exact ⟨atom S x, ⟨⟨x, rfl⟩, hx⟩, mem_atom_self S x⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, hy⟩, hxy⟩
      rw [atom_eq_of_mem S hxy]
      exact hy
  rw [heq]
  refine MeasurableSet.biUnion ((hfin.subset fun a ha => ha.1).countable) ?_
  rintro _ ⟨⟨y, rfl⟩, _⟩
  exact atom_measurable S hfin y

lemma exists_enum [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (ω : Ω)
    (hI : HasIndicators S) (hPc : IsCompact (Prob S))
    (hgood : ∀ X₀ ε, 0 < ε → ∃ μ ∈ Good S ρ ω,
      ρω S ρ ω X₀ - ε < pair (S.toMeasure μ) (S.toFun X₀)) :
    ∃ v : ℕ → 𝒴, (∀ i, v i ∈ Good S ρ ω) ∧
      ∀ X, IsLUB (Set.range fun i => pair (S.toMeasure (v i)) (S.toFun X)) (ρω S ρ ω X) := by
  obtain ⟨xs, hxs⟩ := TopologicalSpace.exists_dense_seq 𝒳
  haveI : CompactSpace (Prob S) := isCompact_iff_compactSpace.1 hPc
  let e : Prob S → (ℕ → ℝ) := fun μ k => pair (S.toMeasure μ.1) (S.toFun (xs k))
  have he : Continuous e :=
    continuous_pi fun k => (S.continuous_pair_Y (xs k)).comp continuous_subtype_val
  have hinj : Function.Injective e := by
    intro μ μ' h
    have h1 : (fun X => pair (S.toMeasure μ.1) (S.toFun X)) =
        fun X => pair (S.toMeasure μ'.1) (S.toFun X) :=
      Continuous.ext_on hxs (S.continuous_pair_X _) (S.continuous_pair_X _)
        (by rintro _ ⟨k, rfl⟩; exact congrFun h k)
    apply Subtype.ext
    apply S.toMeasure_injective
    ext A hA
    obtain ⟨XA, hXA⟩ := hI A hA
    have := congrFun h1 XA
    simp only [hXA, pair_indicator _ hA] at this
    exact this
  haveI : SecondCountableTopology (Prob S) :=
    (he.isClosedEmbedding hinj).isEmbedding.secondCountableTopology
  let G : Set (Prob S) := {μ | μ.1 ∈ Good S ρ ω}
  obtain ⟨μ₀, hμ₀, -⟩ := hgood 0 1 one_pos
  haveI : Nonempty G := ⟨⟨⟨μ₀, hμ₀.1.1⟩, hμ₀⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq G
  refine ⟨fun i => (u i).1.1, fun i => (u i).2, fun X => ⟨?_, ?_⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact (u i).2.2 X
  · intro b hb
    have hcl : IsClosed {g : G | pair (S.toMeasure g.1.1) (S.toFun X) ≤ b} :=
      isClosed_le ((S.continuous_pair_Y X).comp
        (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
    have hsub : Set.range u ⊆ {g : G | pair (S.toMeasure g.1.1) (S.toFun X) ≤ b} := by
      rintro _ ⟨i, rfl⟩
      exact hb ⟨i, rfl⟩
    have hall : ∀ g : G, pair (S.toMeasure g.1.1) (S.toFun X) ≤ b := fun g =>
      hcl.closure_subset_iff.2 hsub (hu g)
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨μ, hμ, hlt⟩ := hgood X ε hε
    have := hall ⟨⟨μ, hμ.1.1⟩, hμ⟩
    simp only at this
    linarith

end Main

end CondRiskMap.Repr.T2Aux

open CondRiskMap.Repr.T2Aux in
open CondRiskMap.Repr MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴] [Nonempty Ω]
    [TopologicalSpace.SeparableSpace 𝒳]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S) (hI : HasIndicators S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ)
    (hK : CondK S ρ) :
    ∃ (ν : ℕ → 𝒴) (κ : ℕ → Ω → 𝒴),
      (∀ i, ν i ∈ Prob S) ∧ (∀ i ω, κ i ω ∈ Prob S) ∧ (∀ i, IsWeakStarMeasurable S (κ i)) ∧
      (∀ i, IsCondProb S (ν i) (κ i)) ∧
      ∀ X ω, IsLUB (Set.range fun i => pair (S.toMeasure (κ i ω)) (S.toFun X)) (ρω S ρ ω X) := by
  have hgood : ∀ ω X₀ ε, 0 < ε → ∃ μ ∈ Good S ρ ω,
      ρω S ρ ω X₀ - ε < pair (S.toMeasure μ) (S.toFun X₀) :=
    fun ω X₀ ε hε => exists_good S ρ hC hC' hρ hph hlsc ω X₀ hε
  have hne : ∀ ω, ∃ μ, μ ∈ ProbGiven S ω := fun ω => by
    obtain ⟨μ, hμ, -⟩ := hgood ω 0 1 one_pos
    exact ⟨μ, hμ.1⟩
  have hfin := atoms_finite S hI hK.1 hne
  have hmeas := atom_measurable S hfin
  choose v hv using fun ω => exists_enum S ρ ω hI hK.1 (hgood ω)
  let rep : Set Ω → Ω := fun a => Classical.epsilon fun x => x ∈ a
  have hrep : ∀ ω, rep (atom S ω) ∈ atom S ω := fun ω =>
    Classical.epsilon_spec (p := fun x => x ∈ atom S ω) ⟨ω, mem_atom_self S ω⟩
  let κ : ℕ → Ω → 𝒴 := fun i ω => v (rep (atom S ω)) i
  have hκgood : ∀ i ω, κ i ω ∈ Good S ρ ω := fun i ω => by
    have := (hv (rep (atom S ω))).1 i
    rwa [Good_eq_of_mem S ρ hρ.1 (hrep ω)] at this
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  refine ⟨fun i => κ i ω₀, κ, fun i => (hκgood i ω₀).1.1, fun i ω => (hκgood i ω).1.1,
    ?_, ?_, ?_⟩
  · intro i X
    exact atom_fun_measurable S hfin fun a => pair (S.toMeasure (v (rep a) i)) (S.toFun X)
  · intro i
    refine ⟨fun A _ => atom_fun_measurable S hfin fun a => S.toMeasure (v (rep a) i) A, ?_⟩
    intro A B hA hB
    obtain ⟨⟨hν0, hν1⟩, hνB⟩ := (hκgood i ω₀).1
    have hE : S.toMeasure (κ i ω₀) (atom S ω₀) = 1 := by
      rw [hνB _ (hmeas ω₀), Set.indicator_of_mem (mem_atom_self S ω₀)]
      rfl
    rw [pair_eq_of_const hν0 hν1 (S.F₁_le _ (hmeas ω₀)) hE _
      (B.indicator (fun ω => S.toMeasure (κ i ω) A) ω₀)]
    · by_cases hωB : ω₀ ∈ B
      · rw [Set.indicator_of_mem hωB]
        have hc : S.toMeasure (κ i ω₀) Bᶜ = 0 := by
          rw [hνB _ hB.compl, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hωB)]
        have hPc := posPart_null hν0 (S.F₁_le _ hB).compl hc
        rw [apply_eq_posPart hν0 hA, apply_eq_posPart hν0 (hA.inter (S.F₁_le _ hB))]
        simp only [Measure.real, measure_inter_conull hPc]
      · rw [Set.indicator_of_notMem hωB]
        have hc : S.toMeasure (κ i ω₀) B = 0 := by
          rw [hνB _ hB, Set.indicator_of_notMem hωB]
        have hPc := posPart_null hν0 (S.F₁_le _ hB) hc
        rw [apply_eq_posPart hν0 (hA.inter (S.F₁_le _ hB))]
        simp only [Measure.real, measure_mono_null Set.inter_subset_right hPc,
          ENNReal.toReal_zero]
    · intro ω hω
      have hat : atom S ω = atom S ω₀ := atom_eq_of_mem S hω
      have hκeq : κ i ω = κ i ω₀ := by simp only [κ, hat]
      by_cases hωB : ω₀ ∈ B
      · rw [Set.indicator_of_mem hωB, Set.indicator_of_mem ((hω B hB).2 hωB), hκeq]
      · rw [Set.indicator_of_notMem hωB,
          Set.indicator_of_notMem (fun h => hωB ((hω B hB).1 h))]
  · intro X ω
    have := (hv (rep (atom S ω))).2 X
    rwa [rhoω_eq_of_mem S ρ hρ.1 (hrep ω)] at this
