-- Prove2me | solution 1 for DiazModulus.interpolation_det_order
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:21:14.344983+00:00
-- url     : https://prove2.me/submissions/ce9e18c4-1777-4cc8-be7f-efc6f85c5c96

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_iteratedDeriv_det_eq_sum
import Theorems.Thm_DiazModulus_iteratedDeriv_iteratedFDeriv_line

open Complex ComplexConjugate

/-! # Order of vanishing of an interpolation determinant (DALAG Lemma 9.2)

Let `Δ(z) = det (D^{σ_μ} f_l (z ζ_μ)(v_μ))` and `Θ = Θₙ(L)` the least total degree of `L` distinct
multi-indices. Each entry is entire, so `Δ` is entire, and it suffices to show
`Δ^{(j)}(0) = 0` whenever `j + Σ σ_μ < Θ` (`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`).
By the Leibniz rule for determinants (`iteratedDeriv_det_eq_sum`) `Δ^{(j)}(0)` is a combination of
determinants `det (∂_z^{q_μ} D^{σ_μ} f_l (z ζ_μ)(v_μ))|_{z=0}` with `Σ q = j`, and by
`iteratedDeriv_iteratedFDeriv_line` each such entry is `D^{m_μ} f_l(0)(w_μ)` with
`m_μ = σ_μ + q_μ`, `Σ m_μ < Θ`. Such a determinant vanishes: expanding each `w_μ i` in the
standard basis, column `μ` is a combination of the columns `(D^{m_μ} f_l(0)(e_{s 1},…,e_{s m_μ}))_l`
over `s : Fin m_μ → Fin n`, and multilinearity of the determinant (in the rows of the transpose)
turns it into a sum of determinants indexed by choices `S`. For a choice `S`, let `κ' μ` count
the fibres of `S μ`; it is a multi-index of degree `m_μ`. If `κ'` is injective then
`Θ ≤ Σ m_μ`, a contradiction; otherwise two columns have the same fibre counts, are equal by the
symmetry of iterated derivatives (`Equiv.ofFiberEquiv`, `ContDiffAt.iteratedFDeriv_comp_perm`),
and the determinant is zero.
-/

namespace C14_A4
open DiazModulus
open scoped ContDiff

/-- Standard basis vector of `ℂⁿ`. -/
def eb {n : ℕ} (k : Fin n) : Fin n → ℂ := fun j => if k = j then 1 else 0

lemma expand {n m : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin m => Fin n → ℂ) ℂ)
    (w : Fin m → Fin n → ℂ) :
    Φ w = ∑ s : Fin m → Fin n, (∏ i, w i (s i)) * Φ (fun i => eb (s i)) := by
  classical
  have hw : w = fun i => ∑ k, w i k • eb k := funext fun i => pi_eq_sum_univ (w i)
  conv_lhs => rw [hw]
  rw [Φ.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Φ.map_smul_univ, smul_eq_mul]

lemma rows_eq {n : ℕ} (F : (Fin n → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ) :
    ∀ (a b : ℕ) (s : Fin a → Fin n) (t : Fin b → Fin n),
    (∀ k, (Finset.univ.filter fun i => s i = k).card =
      (Finset.univ.filter fun i => t i = k).card) →
    iteratedFDeriv ℂ a F 0 (fun i => eb (s i)) = iteratedFDeriv ℂ b F 0 (fun i => eb (t i)) := by
  classical
  intro a b s t h
  have hab : a = b := by
    have ha := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := s)
      (fun _ _ => Finset.mem_univ _)
    have hb := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := t)
      (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at ha hb
    rw [ha, hb]; exact Finset.sum_congr rfl fun k _ => h k
  subst hab
  have e : ∀ c, {i // s i = c} ≃ {i // t i = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  have hπ : ∀ i, t (Equiv.ofFiberEquiv e i) = s i := fun i => Equiv.ofFiberEquiv_map e i
  have : (fun i => eb (s i)) = (fun i => eb (t i)) ∘ (Equiv.ofFiberEquiv e) := by
    funext i; rw [Function.comp_apply, hπ]
  rw [this]
  exact (hF.contDiff (n := ω)).contDiffAt.iteratedFDeriv_comp_perm _ _

lemma det_zero {n L : ℕ} (f : Fin L → (Fin n → ℂ) → ℂ) (hf : ∀ l, AnalyticOnNhd ℂ (f l) Set.univ)
    (m : Fin L → ℕ) (w : (μ : Fin L) → Fin (m μ) → Fin n → ℂ)
    (hm : ∑ μ, m μ <
      sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i}) :
    (Matrix.of fun l μ => iteratedFDeriv ℂ (m μ) (f l) 0 (w μ)).det = 0 := by
  classical
  rw [← Matrix.det_transpose]
  set R : (μ : Fin L) → (Fin (m μ) → Fin n) → Fin L → ℂ :=
    fun μ s l => iteratedFDeriv ℂ (m μ) (f l) 0 (fun i => eb (s i)) with hR
  set c : (μ : Fin L) → (Fin (m μ) → Fin n) → ℂ := fun μ s => ∏ i, w μ i (s i) with hc
  have hT : Matrix.transpose (Matrix.of fun l μ => iteratedFDeriv ℂ (m μ) (f l) 0 (w μ)) =
      fun μ => ∑ s, c μ s • R μ s := by
    funext μ l
    simp only [Matrix.transpose_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hR, hc]
    exact expand _ _
  rw [hT]
  change (Matrix.detRowAlternating : (Fin L → ℂ) [⋀^Fin L]→ₗ[ℂ] ℂ).toMultilinearMap
    (fun μ => ∑ s, c μ s • R μ s) = 0
  rw [MultilinearMap.map_sum]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [MultilinearMap.map_smul_univ]
  set κ' : Fin L → Fin n → ℕ := fun μ k => (Finset.univ.filter fun i => S μ i = k).card with hκ
  have hκsum : ∀ μ, ∑ k, κ' μ k = m μ := fun μ => by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := S μ)
      (fun _ _ => Finset.mem_univ _)
    simpa [hκ] using this.symm
  by_cases hinj : Function.Injective κ'
  · exfalso
    have hle := Nat.sInf_le (show ∑ l, ∑ i, κ' l i ∈
      {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} from
      ⟨κ', hinj, rfl⟩)
    simp only [hκsum] at hle
    omega
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨μ1, μ2, heq, hne⟩ := hinj
    have hrow : R μ1 (S μ1) = R μ2 (S μ2) :=
      funext fun l => rows_eq (f l) (hf l) _ _ _ _ (fun k => congrFun heq k)
    have h0 : (Matrix.detRowAlternating : (Fin L → ℂ) [⋀^Fin L]→ₗ[ℂ] ℂ).toMultilinearMap
        (fun μ => R μ (S μ)) = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ (fun μ => R μ (S μ)) hrow hne
    rw [h0, smul_zero]

lemma g_diff {n N : ℕ} (F : (Fin n → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (ζ : Fin n → ℂ) (w : Fin N → Fin n → ℂ) :
    Differentiable ℂ (fun z : ℂ => iteratedFDeriv ℂ N F (z • ζ) w) := by
  have hΦ : Differentiable ℂ (iteratedFDeriv ℂ N F) :=
    (hF.contDiff (n := ((N + 1 : ℕ) : WithTop ℕ∞))).differentiable_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self N)
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin N => Fin n → ℂ) ℂ w).differentiable.comp
    (hΦ.comp (differentiable_id.smul_const ζ))

end C14_A4

open DiazModulus C14_A4 in
theorem solution {n L : ℕ} (f : Fin L → (Fin n → ℂ) → ℂ)
    (hf : ∀ l, AnalyticOnNhd ℂ (f l) Set.univ) (ζ : Fin L → Fin n → ℂ) (σ : Fin L → ℕ)
    (v : (μ : Fin L) → Fin (σ μ) → Fin n → ℂ) :
    ((sInf {S | ∃ κ' : Fin (L) → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun z : ℂ =>
        (Matrix.of fun l μ => iteratedFDeriv ℂ (σ μ) (f l) (z • ζ μ) (v μ)).det) 0
        + ∑ μ, (σ μ : ℕ∞) := by
  classical
  have hg : ∀ l μ, Differentiable ℂ
      ((fun l μ z => iteratedFDeriv ℂ (σ μ) (f l) (z • ζ μ) (v μ)) l μ) :=
    fun l μ => g_diff (f l) (hf l) (ζ μ) (v μ)
  have hΔ : Differentiable ℂ (fun z : ℂ =>
      (Matrix.of fun l μ => iteratedFDeriv ℂ (σ μ) (f l) (z • ζ μ) (v μ)).det) := by
    have : (fun z : ℂ => (Matrix.of fun l μ => iteratedFDeriv ℂ (σ μ) (f l) (z • ζ μ) (v μ)).det)
        = fun x => ∑ π : Equiv.Perm (Fin L), ((Equiv.Perm.sign π : ℤ) : ℂ) *
          ∏ μ, iteratedFDeriv ℂ (σ μ) (f (π μ)) (x • ζ μ) (v μ) := by
      funext x; rw [Matrix.det_apply']; rfl
    rw [this]
    intro x
    exact DifferentiableAt.fun_sum fun π _ => (DifferentiableAt.fun_finsetProd
      fun μ _ => hg (π μ) μ x).const_mul _
  have hstep : ∀ j, j + ∑ μ, σ μ <
      sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} →
      iteratedDeriv j (fun z : ℂ =>
        (Matrix.of fun l μ => iteratedFDeriv ℂ (σ μ) (f l) (z • ζ μ) (v μ)).det) 0 = 0 := by
    intro j hj
    have h2 := DiazModulus.iteratedDeriv_det_eq_sum _ hg j 0
    beta_reduce at h2
    rw [h2]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' : ∑ μ, q μ = j := Finset.Nat.mem_antidiagonalTuple.mp hq
    have hM : (Matrix.of fun l μ =>
        iteratedDeriv (q μ) (fun z : ℂ => iteratedFDeriv ℂ (σ μ) (f l) (z • ζ μ) (v μ)) 0) =
        Matrix.of fun l μ => iteratedFDeriv ℂ (σ μ + q μ) (f l) 0
          (Fin.append (v μ) (fun _ : Fin (q μ) => ζ μ)) := by
      ext l μ
      exact DiazModulus.iteratedDeriv_iteratedFDeriv_line (f l) (hf l) (ζ μ) (σ μ) (q μ) (v μ)
    rw [hM, det_zero f hf (fun μ => σ μ + q μ) _ (by rw [Finset.sum_add_distrib, hq']; omega),
      mul_zero]
  rw [← Nat.cast_sum]
  by_cases hle : sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧
      S = ∑ l, ∑ i, κ' l i} ≤ ∑ μ, σ μ
  · exact (Nat.cast_le.mpr hle).trans le_add_self
  · have hN := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hΔ.analyticAt 0)
      (n := sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧
        S = ∑ l, ∑ i, κ' l i} - ∑ μ, σ μ)).mpr fun i hi => hstep i (by omega)
    calc ((sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧
            S = ∑ l, ∑ i, κ' l i} : ℕ) : ℕ∞)
        = ((sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧
            S = ∑ l, ∑ i, κ' l i} - ∑ μ, σ μ : ℕ) : ℕ∞) + ((∑ μ, σ μ : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
      _ ≤ _ := add_le_add hN le_rfl
