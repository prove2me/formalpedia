-- Prove2me | solution 1 for BosonicLearn.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T07:24:33.279091+00:00
-- url     : https://prove2.me/submissions/4bc5cee5-db4c-406e-8e91-b2731f7c07d8

import Mathlib
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_promiseClass
import Definitions.Def_BosonicLearn_IsPassive
import Theorems.Thm_BosonicLearn_proposition_5
import Theorems.Thm_BosonicLearn_lemma_12
import Theorems.Thm_BosonicLearn_fugacityFamily_promiseClass
import Theorems.Thm_BosonicLearn_fugacityFamily_separable
import Theorems.Thm_BosonicLearn_priorMu_prob

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize NuclearExpansion IsDensity IsTraceClass)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Rank-one representations with a countable index set -/

/-- `NucRep X w`: the matrix `X` is a sum `∑ₐ |Lₐ⟩⟨Rₐ|` over a countable index set, with total weight
`∑ₐ ‖Lₐ‖‖Rₐ‖ = w`. -/
private def NucRep {I : Type} (X : Matrix I I ℂ) (w : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (L R : ι → Hilbert I),
    HasSum (fun a => ‖L a‖ * ‖R a‖) w ∧ ∀ i j, HasSum (fun a => L a i * star (R a j)) (X i j)

/-- A representation of weight `w` bounds the trace size by `w`: re-index it by `ℕ`. -/
private lemma rep_traceSize {I : Type} {X : Matrix I I ℂ} {w : ℝ} (h : NucRep X w) :
    traceSize X ≤ ENNReal.ofReal w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := h
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  have key1 : (fun n => ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖) =
      Function.extend g (fun a => ‖L a‖ * ‖R a‖) 0 := by
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  have key2 : ∀ i j, (fun n => (Function.extend g L 0 n) i * star ((Function.extend g R 0 n) j)) =
      Function.extend g (fun a => L a i * star (R a j)) 0 := by
    intro i j
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  let e : NuclearExpansion X :=
    { left := Function.extend g L 0
      right := Function.extend g R 0
      summable := by
        rw [key1]
        exact (summable_extend_zero hg).mpr hw.summable
      coefficients := by
        intro i j
        rw [key2 i j, tsum_extend_zero hg]
        exact (hX i j).tsum_eq.symm }
  refine (iInf_le _ e).trans (le_of_eq ?_)
  congr 1
  show ∑' n, ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖ = w
  rw [key1, tsum_extend_zero hg]
  exact hw.tsum_eq

private lemma rep_add {I : Type} {X Y : Matrix I I ℂ} {w v : ℝ} (hX : NucRep X w) (hY : NucRep Y v) :
    NucRep (X + Y) (w + v) := by
  obtain ⟨ι₁, hι₁, L₁, R₁, hw, hX⟩ := hX
  obtain ⟨ι₂, hι₂, L₂, R₂, hv, hY⟩ := hY
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim L₁ L₂, Sum.elim R₁ R₂, ?_, fun i j => ?_⟩
  · exact HasSum.sum (f := fun a => ‖Sum.elim L₁ L₂ a‖ * ‖Sum.elim R₁ R₂ a‖) hw hv
  · exact HasSum.sum (f := fun a => Sum.elim L₁ L₂ a i * star (Sum.elim R₁ R₂ a j)) (hX i j) (hY i j)

/-- A nuclear expansion is a representation with the same weight. -/
private lemma rep_of_expansion {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    NucRep X (∑' n, ‖e.left n‖ * ‖e.right n‖) := by
  refine ⟨ℕ, inferInstance, e.left, e.right, e.summable.hasSum, fun i j => ?_⟩
  rw [e.coefficients i j]
  have h : Summable fun a => e.left a i * star (e.right a j) := by
    refine Summable.of_norm_bounded e.summable fun a => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) (e.left a) i)
      (lp.norm_apply_le_norm (by norm_num) (e.right a) j) (norm_nonneg _) (norm_nonneg _)
  exact h.hasSum

/-- Subadditivity of the trace norm. -/
private lemma traceSize_add_le {I : Type} (X Y : Matrix I I ℂ) :
    traceSize (X + Y) ≤ traceSize X + traceSize Y := by
  have key : ∀ (eX : NuclearExpansion X) (eY : NuclearExpansion Y), traceSize (X + Y) ≤
      ENNReal.ofReal (∑' n, ‖eX.left n‖ * ‖eX.right n‖) +
        ENNReal.ofReal (∑' n, ‖eY.left n‖ * ‖eY.right n‖) := by
    intro eX eY
    refine (rep_traceSize (rep_add (rep_of_expansion eX) (rep_of_expansion eY))).trans ?_
    rw [ENNReal.ofReal_add (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  show traceSize (X + Y) ≤
    (⨅ e : NuclearExpansion X, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)) +
      ⨅ e : NuclearExpansion Y, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)
  rw [ENNReal.iInf_add]
  refine le_iInf fun eX => ?_
  rw [ENNReal.add_iInf]
  exact le_iInf fun eY => key eX eY

private lemma rep_neg {I : Type} {X : Matrix I I ℂ} {w : ℝ} (hX : NucRep X w) : NucRep (-X) w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := hX
  refine ⟨ι, hι, fun a => -L a, R, ?_, fun i j => ?_⟩
  · simpa using hw
  · have h := (hX i j).neg
    simpa [neg_mul] using h


/-- Symmetry of the trace norm under negation. -/
private lemma traceSize_neg {I : Type} (X : Matrix I I ℂ) : traceSize (-X) = traceSize X := by
  have key : ∀ Y : Matrix I I ℂ, traceSize (-Y) ≤ traceSize Y := by
    intro Y
    show traceSize (-Y) ≤ ⨅ e : NuclearExpansion Y, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)
    exact le_iInf fun e => rep_traceSize (rep_neg (rep_of_expansion e))
  refine le_antisymm (key X) ?_
  have h := key (-X)
  rwa [neg_neg] at h

private lemma traceSize_sub_comm {I : Type} (A B : Matrix I I ℂ) :
    traceSize (A - B) = traceSize (B - A) := by
  rw [← neg_sub B A, traceSize_neg]

private lemma traceSize_sub_le {I : Type} (A B C : Matrix I I ℂ) :
    traceSize (A - C) ≤ traceSize (A - B) + traceSize (B - C) := by
  rw [← sub_add_sub_cancel A B C]
  exact traceSize_add_le _ _

/-! ### A measurable decoder -/

/-- From an estimate of the state one can measurably read off a point of `G_supp` whose state is close to
every state of the family that is close to the estimate. -/
private lemma exists_decoder (n : ℕ) (ν ξ ε : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1 / 32) (hε : 0 < ε)
    (hfam : ∀ X ∈ Gsupp n, ∃ ρ : State (Occupation (Fin n)),
      ρ.coefficients = fugacityCoeff (fugacityFamily ν ξ X)) :
    ∃ dec : State (Occupation (Fin n)) → Herm0 n, Measurable dec ∧ (∀ σ, dec σ ∈ Gsupp n) ∧
      ∀ X ∈ Gsupp n, ∀ σ : State (Occupation (Fin n)),
        traceSize (σ.coefficients - fugacityCoeff (fugacityFamily ν ξ X)) ≤ ENNReal.ofReal (2 * ε) →
        traceSize (fugacityCoeff (fugacityFamily ν ξ (dec σ)) -
          fugacityCoeff (fugacityFamily ν ξ X)) < ENNReal.ofReal (5 * ε) := by
  obtain ⟨D, hD, hsep⟩ := fugacityFamily_separable n ν ξ hν0 hν1 hξ0 hξ1
  choose sD hsD using fun k => hfam (D k) (hD k)
  let U : ℕ → Set (State (Occupation (Fin n))) := fun k =>
    {σ | traceSize (σ.coefficients - (sD k).coefficients) < ENNReal.ofReal (3 * ε)}
  have hUopen : ∀ k, MeasurableSet (U k) := by
    intro k
    have ho : IsOpen (U k) :=
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨sD k, 3 * ε, by positivity, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ho
  let p : ℕ → State (Occupation (Fin n)) → Prop := fun k σ => σ ∈ U k ∨ ∀ j, σ ∉ U j
  have hp : ∀ k, MeasurableSet {σ | p k σ} := by
    intro k
    have e : {σ | p k σ} = U k ∪ ⋂ j, (U j)ᶜ := by
      ext σ
      simp [p]
    rw [e]
    exact (hUopen k).union (MeasurableSet.iInter fun j => (hUopen j).compl)
  have h : ∀ σ, ∃ k, p k σ := by
    intro σ
    by_cases hσ : ∃ k, σ ∈ U k
    · obtain ⟨k, hk⟩ := hσ
      exact ⟨k, Or.inl hk⟩
    · exact ⟨0, Or.inr fun j hj => hσ ⟨j, hj⟩⟩
  refine ⟨fun σ => D (Nat.find (h σ)),
    Measurable.find (f := fun k _ => D k) (fun k => measurable_const) hp h, fun σ => hD _, ?_⟩
  intro X hX σ hσ
  obtain ⟨k₀, hk₀⟩ := hsep X hX ε hε
  -- `σ` lies in `U k₀`
  have hσk₀ : σ ∈ U k₀ := by
    show traceSize (σ.coefficients - (sD k₀).coefficients) < ENNReal.ofReal (3 * ε)
    rw [hsD k₀]
    refine (traceSize_sub_le _ (fugacityCoeff (fugacityFamily ν ξ X)) _).trans_lt ?_
    have h3 : ENNReal.ofReal (3 * ε) = ENNReal.ofReal (2 * ε) + ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) hε.le]
      congr 1
      ring
    rw [h3]
    exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hσ) hσ hk₀
  -- hence the selected index also has `σ` in its set
  have hsel : σ ∈ U (Nat.find (h σ)) := by
    rcases Nat.find_spec (h σ) with h1 | h1
    · exact h1
    · exact absurd hσk₀ (h1 k₀)
  have hsel' : traceSize (σ.coefficients -
      fugacityCoeff (fugacityFamily ν ξ (D (Nat.find (h σ))))) < ENNReal.ofReal (3 * ε) := by
    have h1 : traceSize (σ.coefficients - (sD (Nat.find (h σ))).coefficients) <
        ENNReal.ofReal (3 * ε) := hsel
    rwa [hsD] at h1
  show traceSize (fugacityCoeff (fugacityFamily ν ξ (D (Nat.find (h σ)))) -
    fugacityCoeff (fugacityFamily ν ξ X)) < ENNReal.ofReal (5 * ε)
  refine (traceSize_sub_le _ σ.coefficients _).trans_lt ?_
  rw [traceSize_sub_comm]
  have h5 : ENNReal.ofReal (5 * ε) = ENNReal.ofReal (3 * ε) + ENNReal.ofReal (2 * ε) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [h5]
  exact ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hσ) hsel' hσ

/-! ### The statement -/

theorem solution :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O)
        (est : Kernel (Fin N → O) (State (Occupation (Fin n)))), IsMarkovKernel est →
        (∀ ρ ∈ promiseClass n ν, IsPassive ρ →
          ENNReal.ofReal (2 / 3) ≤ successProb S est ρ.coefficients ε) →
        c * ((n : ℝ) ^ 2 / (ν * ε ^ 2)) ≤ N := by
  obtain ⟨ξ₀, hξ₀pos, hξ₀lt, a₀, ha₀, h5⟩ := proposition_5
  obtain ⟨κ, hκ, n₁, h5'⟩ := h5 a₀ ha₀ le_rfl (1 / 2) (by norm_num)
  obtain ⟨Ca, hCa, αa, hαa, h12⟩ := lemma_12 (a₀ / 2) (by positivity)
  have hmin : 0 < min αa ξ₀ := lt_min hαa hξ₀pos
  refine ⟨min αa ξ₀ * Ca / 5, by positivity, κ * Ca ^ 2 / 25, by positivity, max n₁ 1,
    fun n hn ν hν1 hν2 ε hε0 hε1 N O _ S est hest hlearn => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn0 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnpos : (0 : ℝ) < n := by linarith
  have hνpos : 0 < ν := lt_of_lt_of_le (by positivity) hν1
  have hnν : 1 ≤ (n : ℝ) * ν := by
    have h := (div_le_iff₀ hnpos).mp hν1
    linarith
  set s : ℝ := Real.sqrt (n * ν) with hs
  have hs1 : 1 ≤ s := by
    rw [hs]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (n * ν) := Real.sqrt_le_sqrt hnν
  have hspos : 0 < s := by linarith
  have hs2 : s ^ 2 = n * ν := Real.sq_sqrt (by positivity)
  set ξ : ℝ := 5 * ε / (Ca * s) with hξ
  have hξpos : 0 < ξ := by positivity
  have hξs : ξ * s = 5 * ε / Ca := by
    rw [hξ]
    field_simp
  have h5ε : 5 * ε / Ca < min αa ξ₀ := by
    rw [div_lt_iff₀ hCa]
    linarith
  have hξle : ξ ≤ 5 * ε / Ca := by
    rw [← hξs]
    nlinarith
  have hξξ₀ : ξ ≤ ξ₀ := (hξle.trans h5ε.le).trans (min_le_right _ _)
  have hξ32 : ξ < 1 / 32 := lt_of_le_of_lt hξξ₀ hξ₀lt
  have hξα : ξ ≤ αa / s := by
    rw [le_div_iff₀ hspos, hξs]
    exact h5ε.le.trans (min_le_left _ _)
  -- the number of copies is below the threshold of Proposition 5
  have hNκ : (N : ℝ) * ν ^ 2 * ξ ^ 2 ≤ κ * n := by
    have hξ2 : ξ ^ 2 * (Ca ^ 2 * (n * ν)) = 25 * ε ^ 2 := by
      rw [← hs2, hξ]
      field_simp
      norm_num
    have h1 : (N : ℝ) * (ν * ε ^ 2) < κ * Ca ^ 2 / 25 * n ^ 2 := by
      have h := hcon
      rw [← mul_div_assoc, lt_div_iff₀ (by positivity)] at h
      exact h
    have hpos : 0 < Ca ^ 2 * (n * ν) := by positivity
    have h2 : (N : ℝ) * ν ^ 2 * ξ ^ 2 * (Ca ^ 2 * (n * ν)) ≤ κ * n * (Ca ^ 2 * (n * ν)) := by
      calc (N : ℝ) * ν ^ 2 * ξ ^ 2 * (Ca ^ 2 * (n * ν))
          = N * ν ^ 2 * (ξ ^ 2 * (Ca ^ 2 * (n * ν))) := by ring
        _ = 25 * ν * (N * (ν * ε ^ 2)) := by
            rw [hξ2]
            ring
        _ ≤ 25 * ν * (κ * Ca ^ 2 / 25 * n ^ 2) := mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ = κ * n * (Ca ^ 2 * (n * ν)) := by ring
    exact le_of_mul_le_mul_right h2 hpos
  -- the family and the decoder
  have hfam := fugacityFamily_promiseClass n ν ξ hνpos hν2 hξpos hξ32
  obtain ⟨dec, hdecm, hdecG, hdec⟩ := exists_decoder n ν ξ ε hνpos hν2 hξpos hξ32 hε0
    (fun X hX => by
      obtain ⟨ρ, hρ, -, -⟩ := hfam X hX
      exact ⟨ρ, hρ⟩)
  have hA := h5' n hn1 ν hν1 hν2 ξ hξpos hξξ₀ N hNκ O S (est.map dec)
    (Kernel.IsMarkovKernel.map est hdecm)
  obtain ⟨hprob, hsupp⟩ := priorMu_prob n
  have hCaξ : Ca * ξ * s = 5 * ε := by
    rw [mul_assoc, hξs]
    field_simp
  -- the learner solves the problem of Proposition 5 with probability at least 2/3
  have hlow : ENNReal.ofReal (2 / 3) ≤
      ∫⁻ X₀, ∫⁻ x, (est.map dec) x {Y | WHMultiplicativity.schattenNorm 1
          ((Y - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a₀ / 2}
        ∂(transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X₀))) ∂(priorMu n) := by
    have hconst : ENNReal.ofReal (2 / 3) = ∫⁻ _X₀ : Herm0 n, ENNReal.ofReal (2 / 3) ∂(priorMu n) := by
      rw [lintegral_const, measure_univ, mul_one]
    rw [hconst]
    refine lintegral_mono_ae (hsupp.mono fun X₀ hX₀ => ?_)
    obtain ⟨ρ, hco, hpas, hprom⟩ := hfam X₀ hX₀
    have h1 := hlearn ρ hprom hpas
    rw [hco] at h1
    refine h1.trans ?_
    unfold successProb
    refine lintegral_mono fun x => ?_
    rw [Kernel.map_apply _ hdecm]
    refine (measure_mono ?_).trans (Measure.le_map_apply hdecm.aemeasurable _)
    intro σ hσ
    show WHMultiplicativity.schattenNorm 1 ((dec σ - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤
      n * a₀ / 2
    by_contra hbig
    rw [not_le] at hbig
    have h12' := h12 n hn0 ν hν1 hν2 ξ hξpos hξ32 hξα X₀ hX₀ (dec σ) (hdecG σ) (by linarith)
    rw [← hs, hCaξ] at h12'
    have hσ' : traceSize (σ.coefficients - fugacityCoeff (fugacityFamily ν ξ X₀)) ≤
        ENNReal.ofReal (2 * ε) := by
      have h2 : traceDist σ.coefficients (fugacityCoeff (fugacityFamily ν ξ X₀)) ≤ ENNReal.ofReal ε :=
        hσ
      unfold traceDist at h2
      rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))] at h2
      refine h2.trans (le_of_eq ?_)
      rw [mul_comm 2 ε, ENNReal.ofReal_mul hε0.le]
      simp
    exact absurd (hdec X₀ hX₀ σ hσ') (not_lt.mpr h12')
  have hfin := hlow.trans hA
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hfin
  norm_num at hfin
