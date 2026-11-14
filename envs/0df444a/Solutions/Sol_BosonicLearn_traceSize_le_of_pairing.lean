-- Prove2me | solution 1 for BosonicLearn.traceSize_le_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:25:01.214091+00:00
-- url     : https://prove2.me/submissions/b96f6ce6-f2d8-4105-b6a6-f869751be873

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

/-!
# Trace norm by duality: `‖A‖₁ ≤ sup_{‖V‖ ≤ 1} |Tr(AV)|` for self-adjoint `A`

* Functional calculus (on an abstract Hilbert space): `A = S² − T²` with `S = √(A⁺)`, `T = √(A⁻)` self-adjoint, and
  for every `ε > 0` a contraction `V_ε = A (|A| + ε)⁻¹` with `‖S² + T² − A V_ε‖ ≤ ε`.
* The hypothesis with `V = V_ε` gives `∑_{u ∈ F} (‖S e_u‖² + ‖T e_u‖²) ≤ c` for every finite `F`.
* `⟨e_u, S² e_v⟩ = ∑_w (S e_w)_u \overline{(S e_w)_v}` is a rank-one representation of the matrix of `S²` of total
  weight `∑_w ‖S e_w‖²`; subtracting the one for `T²` represents the matrix of `A` with weight `≤ c`.
-/

noncomputable section

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

private lemma rep_neg {I : Type} {X : Matrix I I ℂ} {w : ℝ} (hX : NucRep X w) : NucRep (-X) w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := hX
  refine ⟨ι, hι, fun a => -L a, R, ?_, fun i j => ?_⟩
  · simpa using hw
  · have h := (hX i j).neg
    simpa [neg_mul] using h

/-! ### Functional calculus: positive and negative parts, approximate polar decomposition -/

private lemma abs_decomp_scalar (t ε : ℝ) (hε : 0 < ε) :
    ‖max t 0 + max (-t) 0 - t * (t / (|t| + ε))‖ ≤ ε := by
  have h : 0 < |t| + ε := by positivity
  have h1 : max t 0 + max (-t) 0 = |t| := by
    rcases le_total 0 t with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith), abs_of_nonneg h0, add_zero]
    · rw [max_eq_right h0, max_eq_left (by linarith), abs_of_nonpos h0, zero_add]
  have h2 : |t| - t * (t / (|t| + ε)) = ε * |t| / (|t| + ε) := by
    field_simp
    nlinarith [sq_abs t]
  rw [h1, h2, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ h]
  nlinarith [abs_nonneg t]

/-- A bounded self-adjoint operator `A` on a Hilbert space is `S² − T²` with `S, T` self-adjoint
(`S² = A⁺`, `T² = A⁻`), and `|A| = S² + T²` is approximated in norm by `A V` with `V` a contraction. -/
private lemma cfc_decomp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ S T : H →L[ℂ] H, IsSelfAdjoint S ∧ IsSelfAdjoint T ∧ S * S - T * T = A ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : H →L[ℂ] H, ‖V‖ ≤ 1 ∧ ‖S * S + T * T - A * V‖ ≤ ε := by
  have c1 : Continuous (fun t : ℝ => √(max t 0)) := by fun_prop
  have c2 : Continuous (fun t : ℝ => √(max (-t) 0)) := by fun_prop
  have c3 : Continuous (fun t : ℝ => max t 0) := by fun_prop
  have c4 : Continuous (fun t : ℝ => max (-t) 0) := by fun_prop
  have hSS : cfc (fun t : ℝ => √(max t 0)) A * cfc (fun t : ℝ => √(max t 0)) A =
      cfc (fun t : ℝ => max t 0) A := by
    rw [← cfc_mul _ _ A c1.continuousOn c1.continuousOn]
    refine cfc_congr fun t _ => ?_
    exact Real.mul_self_sqrt (le_max_right _ _)
  have hTT : cfc (fun t : ℝ => √(max (-t) 0)) A * cfc (fun t : ℝ => √(max (-t) 0)) A =
      cfc (fun t : ℝ => max (-t) 0) A := by
    rw [← cfc_mul _ _ A c2.continuousOn c2.continuousOn]
    refine cfc_congr fun t _ => ?_
    exact Real.mul_self_sqrt (le_max_right _ _)
  refine ⟨cfc (fun t : ℝ => √(max t 0)) A, cfc (fun t : ℝ => √(max (-t) 0)) A,
    IsSelfAdjoint.cfc, IsSelfAdjoint.cfc, ?_, fun ε hε => ?_⟩
  · rw [hSS, hTT, ← cfc_sub _ _ A c3.continuousOn c4.continuousOn]
    conv_rhs => rw [← cfc_id ℝ A hA]
    refine cfc_congr fun t _ => ?_
    simp only [id]
    rcases le_total 0 t with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · have c5 : Continuous (fun t : ℝ => t / (|t| + ε)) := by
      refine continuous_id.div (by fun_prop) fun t => ?_
      have : 0 < |t| + ε := by positivity
      exact this.ne'
    refine ⟨cfc (fun t : ℝ => t / (|t| + ε)) A, ?_, ?_⟩
    · refine norm_cfc_le zero_le_one fun t _ => ?_
      have h : 0 < |t| + ε := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos h, div_le_one h]
      linarith
    · have hAV : A * cfc (fun t : ℝ => t / (|t| + ε)) A =
          cfc (fun t : ℝ => t * (t / (|t| + ε))) A := by
        rw [cfc_mul (fun t : ℝ => t) _ A continuous_id.continuousOn c5.continuousOn,
          cfc_id' ℝ A hA]
      have c6 : Continuous (fun t : ℝ => max t 0 + max (-t) 0) := c3.add c4
      have c7 : Continuous (fun t : ℝ => t * (t / (|t| + ε))) := continuous_id.mul c5
      rw [hSS, hTT, hAV, ← cfc_add A _ _ c3.continuousOn c4.continuousOn,
        ← cfc_sub _ _ A c6.continuousOn c7.continuousOn]
      exact norm_cfc_le hε.le fun t _ => abs_decomp_scalar t ε hε

/-! ### Matrices of operators on `ℓ²(I)` -/

/-- The basis vector `e_i` of `ℓ²(I)`. -/
private abbrev bv {I : Type} [DecidableEq I] (i : I) : Hilbert I := lp.single 2 i (1 : ℂ)

private lemma inner_bv_left {I : Type} [DecidableEq I] (i : I) (x : Hilbert I) :
    inner ℂ (bv i) x = x i := by
  rw [lp.inner_single_left]
  simp

private lemma inner_bv_right {I : Type} [DecidableEq I] (i : I) (x : Hilbert I) :
    inner ℂ x (bv i) = star (x i) := by
  rw [lp.inner_single_right]
  simp

private lemma norm_bv {I : Type} [DecidableEq I] (i : I) : ‖(bv i : Hilbert I)‖ = 1 := by
  rw [lp.norm_single (by norm_num)]
  simp

/-- Matrix entries of a self-adjoint operator are Hermitian. -/
private lemma entry_symm {I : Type} [DecidableEq I] (S : Hilbert I →L[ℂ] Hilbert I)
    (hS : IsSelfAdjoint S) (u w : I) : (S (bv u)) w = star ((S (bv w)) u) := by
  rw [← inner_bv_left w (S (bv u)), ← inner_bv_right u (S (bv w))]
  exact (hS.isSymmetric (bv w) (bv u)).symm

/-- `⟨e_u, S² e_v⟩ = ∑_w (S e_w)_u * conj (S e_w)_v` for self-adjoint `S`. -/
private lemma sq_entry_hasSum {I : Type} [DecidableEq I] (S : Hilbert I →L[ℂ] Hilbert I)
    (hS : IsSelfAdjoint S) (u v : I) :
    HasSum (fun w => (S (bv w)) u * star ((S (bv w)) v)) (inner ℂ (bv u) ((S * S) (bv v))) := by
  have h1 : inner ℂ (bv u) ((S * S) (bv v)) = inner ℂ (S (bv u)) (S (bv v)) :=
    (hS.isSymmetric (bv u) (S (bv v))).symm
  rw [h1]
  refine (lp.hasSum_inner (𝕜 := ℂ) (S (bv u)) (S (bv v))).congr_fun fun w => ?_
  rw [entry_symm S hS u w, entry_symm S hS v w]
  simp [mul_comm]

/-- `⟨e_u, S² e_u⟩ = ‖S e_u‖²` for self-adjoint `S`. -/
private lemma sq_diag {I : Type} [DecidableEq I] (S : Hilbert I →L[ℂ] Hilbert I)
    (hS : IsSelfAdjoint S) (u : I) :
    inner ℂ (bv u) ((S * S) (bv u)) = ((‖S (bv u)‖ * ‖S (bv u)‖ : ℝ) : ℂ) := by
  have h1 : inner ℂ (bv u) ((S * S) (bv u)) = inner ℂ (S (bv u)) (S (bv u)) :=
    (hS.isSymmetric (bv u) (S (bv u))).symm
  rw [h1, inner_self_eq_norm_sq_to_K, ← sq]
  simp

/-- The matrix of `S²` (`S` self-adjoint, `∑_w ‖S e_w‖² = t`) is a sum of rank-one arrays `|S e_w⟩⟨S e_w|`
of total weight `t`. -/
private lemma rep_sq {I : Type} [DecidableEq I] [Countable I] (S : Hilbert I →L[ℂ] Hilbert I)
    (hS : IsSelfAdjoint S) (t : ℝ) (ht : HasSum (fun w : I => ‖S (bv w)‖ * ‖S (bv w)‖) t) :
    NucRep (fun u v : I => inner ℂ (bv u : Hilbert I) ((S * S) (bv v))) t :=
  ⟨I, inferInstance, fun w => S (bv w), fun w => S (bv w), ht, fun u v => sq_entry_hasSum S hS u v⟩

/-- The pairing hypothesis bounds the finite partial traces of `|A| = S² + T²`. -/
private lemma diag_bound {I : Type} [DecidableEq I] (A S T : Hilbert I →L[ℂ] Hilbert I)
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (c : ℝ)
    (hV : ∀ ε : ℝ, 0 < ε → ∃ V : Hilbert I →L[ℂ] Hilbert I, ‖V‖ ≤ 1 ∧ ‖S * S + T * T - A * V‖ ≤ ε)
    (h : ∀ V : Hilbert I →L[ℂ] Hilbert I, ‖V‖ ≤ 1 → ∀ F : Finset I,
      ‖∑ u ∈ F, inner ℂ (bv u : Hilbert I) (A (V (bv u)))‖ ≤ c) (F : Finset I) :
    ∑ u ∈ F, (‖S (bv u)‖ * ‖S (bv u)‖ + ‖T (bv u)‖ * ‖T (bv u)‖) ≤ c := by
  have key : ∀ ε : ℝ, 0 < ε →
      ∑ u ∈ F, (‖S (bv u)‖ * ‖S (bv u)‖ + ‖T (bv u)‖ * ‖T (bv u)‖) ≤ c + F.card * ε := by
    intro ε hε
    obtain ⟨V, hV1, hV2⟩ := hV ε hε
    have e1 : ((∑ u ∈ F, (‖S (bv u)‖ * ‖S (bv u)‖ + ‖T (bv u)‖ * ‖T (bv u)‖) : ℝ) : ℂ) =
        ∑ u ∈ F, inner ℂ (bv u : Hilbert I) (A (V (bv u))) +
          ∑ u ∈ F, inner ℂ (bv u : Hilbert I) ((S * S + T * T - A * V) (bv u)) := by
      rw [← Finset.sum_add_distrib, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← inner_add_right]
      have h3 : A (V (bv u)) + (S * S + T * T - A * V) (bv u) = (S * S) (bv u) + (T * T) (bv u) := by
        simp
      rw [h3, inner_add_right, sq_diag S hS, sq_diag T hT, Complex.ofReal_add]
    have e2 : ∀ u ∈ F, ‖inner ℂ (bv u : Hilbert I) ((S * S + T * T - A * V) (bv u))‖ ≤ ε := by
      intro u _
      calc ‖inner ℂ (bv u : Hilbert I) ((S * S + T * T - A * V) (bv u))‖
          ≤ ‖(bv u : Hilbert I)‖ * ‖(S * S + T * T - A * V) (bv u)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖S * S + T * T - A * V‖ * 1) := by
            rw [norm_bv]
            refine mul_le_mul_of_nonneg_left ?_ zero_le_one
            exact ((S * S + T * T - A * V).le_opNorm _).trans (by rw [norm_bv])
        _ ≤ ε := by simpa using hV2
    calc ∑ u ∈ F, (‖S (bv u)‖ * ‖S (bv u)‖ + ‖T (bv u)‖ * ‖T (bv u)‖)
        ≤ ‖((∑ u ∈ F, (‖S (bv u)‖ * ‖S (bv u)‖ + ‖T (bv u)‖ * ‖T (bv u)‖) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real]
          exact le_abs_self _
      _ ≤ ‖∑ u ∈ F, inner ℂ (bv u : Hilbert I) (A (V (bv u)))‖ +
            ‖∑ u ∈ F, inner ℂ (bv u : Hilbert I) ((S * S + T * T - A * V) (bv u))‖ := by
          rw [e1]
          exact norm_add_le _ _
      _ ≤ c + F.card * ε := by
          refine add_le_add (h V hV1 F) ?_
          refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ e2).trans ?_)
          simp
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hcard : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have h1 := key (δ / (F.card + 1)) (by positivity)
  have h2 : (F.card : ℝ) * (δ / (F.card + 1)) ≤ δ := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem solution {I : Type} [DecidableEq I] [Countable I] (A : Hilbert I →L[ℂ] Hilbert I)
    (hA : IsSelfAdjoint A) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ V : Hilbert I →L[ℂ] Hilbert I, ‖V‖ ≤ 1 → ∀ F : Finset I,
      ‖∑ u ∈ F, inner ℂ (lp.single 2 u (1 : ℂ) : Hilbert I) (A (V (lp.single 2 u (1 : ℂ))))‖ ≤ c) :
    traceSize (fun u v : I => inner ℂ (lp.single 2 u (1 : ℂ) : Hilbert I) (A (lp.single 2 v (1 : ℂ)))) ≤
      ENNReal.ofReal c := by
  obtain ⟨S, T, hS, hT, hST, hV⟩ := cfc_decomp A hA
  have hb := diag_bound A S T hS hT c hV h
  have hsum : Summable (fun u : I => ‖S (bv u)‖ * ‖S (bv u)‖ + ‖T (bv u)‖ * ‖T (bv u)‖) :=
    summable_of_sum_le (fun u => by positivity) hb
  have hsS : Summable (fun u : I => ‖S (bv u)‖ * ‖S (bv u)‖) :=
    Summable.of_nonneg_of_le (fun u => by positivity)
      (fun u => le_add_of_nonneg_right (by positivity)) hsum
  have hsT : Summable (fun u : I => ‖T (bv u)‖ * ‖T (bv u)‖) :=
    Summable.of_nonneg_of_le (fun u => by positivity)
      (fun u => le_add_of_nonneg_left (by positivity)) hsum
  have R := rep_add (rep_sq S hS _ hsS.hasSum) (rep_neg (rep_sq T hT _ hsT.hasSum))
  have hX : (fun u v : I => inner ℂ (lp.single 2 u (1 : ℂ) : Hilbert I) (A (lp.single 2 v (1 : ℂ)))) =
      (fun u v : I => inner ℂ (bv u : Hilbert I) ((S * S) (bv v))) +
        -(fun u v : I => inner ℂ (bv u : Hilbert I) ((T * T) (bv v))) := by
    funext u v
    rw [← hST]
    simp [sub_eq_add_neg]
  rw [hX]
  refine (rep_traceSize R).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← hsS.tsum_add hsT]
  exact hsum.tsum_le_of_sum_le hb
