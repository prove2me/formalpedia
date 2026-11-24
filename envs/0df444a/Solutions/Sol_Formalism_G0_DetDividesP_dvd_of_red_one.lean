-- Prove2me | solution 1 for Formalism.G0.DetDividesP.dvd_of_red_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:47.138304+00:00
-- url     : https://prove2.me/submissions/35bc3273-2cfd-43eb-9450-2fea94337967

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_msMat_eval0
import Theorems.Thm_Formalism_G0_DetDividesP_aeval_detLetters
import Theorems.Thm_Formalism_G0_DetDividesP_det_Tm_ne_zero
import Theorems.Thm_Formalism_G0_DetDividesP_adj_Tm_ne_zero
import Theorems.Thm_Formalism_G0_DetDividesP_rho_cc
import Theorems.Thm_Formalism_G0_DetDividesP_coprime_det_cc
import Theorems.Thm_Formalism_G0_DetDividesP_aeval_X_comp
import Theorems.Thm_Formalism_G0_DetDividesP_conj_diagonal_last_zero
import Theorems.Thm_Formalism_G0_DetDividesP_rename_detLetters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A)
    (G : MvPolynomial (ι × Fin r) K) (h : Red A G 1) : detLetters (K := K) A ∣ G := by
  classical
  set F' := MvPolynomial ((ι × Fin r) ⊕ ι) K
  let L := FractionRing F'
  let am : F' →+* L := algebraMap F' L
  have ham : Function.Injective am := IsFractionRing.injective F' L
  set T := Tm K A with hT
  set Dt := T.det with hDt
  set ψ := T.adjugate.mulVec (Wv K A) with hψ
  set c := ψ (lst hr) with hcdef
  have hDt0 : Dt ≠ 0 := det_Tm_ne_zero A hA
  have hc0 : c ≠ 0 := by
    intro h0
    have := rho_cc (K := K) A hA (lst hr) (lst hr)
    rw [← hψ, ← hcdef, h0, map_zero] at this
    exact adj_Tm_ne_zero A hA (lst hr) (lst hr) this.symm
  have hamc : am c ≠ 0 := fun h0 => hc0 (ham (by rw [h0, map_zero]))
  let φ : Fin r → L := fun b => am (ψ b) / am c
  have hφ : φ (lst hr) = 1 := div_self hamc
  let g := gU (lst hr) φ hφ
  let Y : ι × Fin r → L := fun p => am (X (Sum.inl p))
  have hY : MvPolynomial.aeval Y (detLetters (K := K) A) = am Dt := by
    rw [aeval_detLetters, hDt, RingHom.map_det]; congr 1
  have hdiv := h L g Y (by rw [hY]; exact fun h0 => hDt0 (ham (by rw [h0, map_zero])))
  have hM0 : ∀ a b, ((msMat g) a b).eval 0 = (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a b := by
    intro a b
    have := congrFun (congrFun (msMat_eval0 g) a) b
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this
    rw [this, conj_diagonal_last_zero hr φ hφ]
  have h0 : MvPolynomial.aeval (fun p => (ptA A g Y p).eval 0) G = 0 := by
    obtain ⟨q, hq⟩ := hdiv
    have e1 := congrArg (fun z => (Polynomial.aeval (0 : L)).restrictScalars K z) hq
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at e1
    simpa [Polynomial.coe_aeval_eq_eval] using e1
  have hTψ : ∀ l, (∑ b, T l b * ψ b) = Dt * Wv K A l := by
    intro l
    have : T.mulVec ψ = Dt • Wv K A := by
      rw [hψ, Matrix.mulVec_mulVec, Matrix.mul_adjugate, ← hDt, Matrix.smul_mulVec, Matrix.one_mulVec]
    have := congrFun this l
    simpa [Matrix.mulVec, dotProduct] using this
  let f : ι × Fin r → Polynomial F' := fun p => Polynomial.C (X (Sum.inl p)) -
    (if p.2 = lst hr ∧ p.1 ∈ Set.range A then Polynomial.C (X (Sum.inr p.1)) * Polynomial.X else 0)
  let Hp : Polynomial F' := MvPolynomial.aeval f G
  have hroot : Polynomial.aeval (am Dt / am c) Hp = 0 := by
    have e1 : Polynomial.aeval (am Dt / am c) Hp =
        MvPolynomial.aeval (fun p => Polynomial.aeval (am Dt / am c) (f p)) G := by
      show ((Polynomial.aeval (am Dt / am c)).restrictScalars K) (MvPolynomial.aeval f G) = _
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]; rfl
    rw [e1, ← h0]
    congr 2
    funext p
    obtain ⟨i, a⟩ := p
    by_cases hi : i ∈ Set.range A
    · obtain ⟨l, rfl⟩ := hi
      simp only [ptA, f, Set.mem_range_self, and_true, if_true, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, hM0]
      have hsum : ∑ x, (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a x * Y (A l, x) =
          Y (A l, a) - ((Pi.single (lst hr) (1 : L) : Fin r → L) a) * ∑ x, φ x * Y (A l, x) := by
        simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, sub_mul,
          Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
          if_true, mul_assoc]
        rw [Finset.mul_sum]
      have hφY : ∑ x, φ x * Y (A l, x) = am (Dt * Wv K A l) / am c := by
        rw [← hTψ l, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [φ, Y, T, Tm, Matrix.of_apply, map_mul]
        ring
      rw [hsum, hφY]
      by_cases ha : a = lst hr
      · subst ha
        simp only [if_true, map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, Pi.single_eq_same,
          one_mul, Wv, Y]
        rw [mul_div_assoc', mul_comm (am (X (Sum.inr (A l)))) (am Dt)]
      · simp only [if_neg ha, sub_zero, Polynomial.aeval_C, Pi.single_apply, zero_mul, Y]
        rfl
    · have hi' : ¬ (a = lst hr ∧ i ∈ Set.range A) := fun h => hi h.2
      simp only [f, ptA, if_neg hi, if_neg hi', sub_zero, Polynomial.eval_C, Polynomial.aeval_C, Y]
      rfl
  have hsc : Polynomial.aeval (am Dt) (Hp.scaleRoots c) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero ham hroot (mem_nonZeroDivisors_of_ne_zero hc0)
  have hisroot : (Hp.scaleRoots c).IsRoot Dt := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at hsc
    exact ham (by rw [hsc, map_zero])
  have hdvd := Polynomial.dvd_term_of_isRoot_of_dvd_terms 0 hisroot
    (fun j hj => dvd_mul_of_dvd_right (dvd_pow_self Dt hj) _)
  rw [pow_zero, mul_one, Polynomial.coeff_scaleRoots, Polynomial.coeff_zero_eq_eval_zero] at hdvd
  have hHp0 : Hp.eval 0 = rename Sum.inl G := by
    have e2 : Hp.eval 0 = MvPolynomial.aeval (fun p => ((Polynomial.aeval (0 : F')).restrictScalars K) (f p)) G := by
      rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      simp [Hp, Polynomial.coe_aeval_eq_eval]
    rw [e2, ← aeval_X_comp]
    congr 2
    funext p
    simp only [f, AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_sub,
      Polynomial.eval_C]
    split_ifs
    · rw [Polynomial.eval_mul, Polynomial.eval_X, mul_zero, sub_zero]
    · rw [Polynomial.eval_zero, sub_zero]
  rw [hHp0] at hdvd
  have hcop := (coprime_det_cc (K := K) A hA (lst hr)).pow_right (n := Hp.natDegree - 0)
  have hD' : Dt ∣ rename Sum.inl G := hcop.dvd_of_dvd_mul_right hdvd
  let ret : F' →ₐ[K] MvPolynomial (ι × Fin r) K := MvPolynomial.aeval (Sum.elim X 0)
  have hret : ∀ q : MvPolynomial (ι × Fin r) K, ret (rename Sum.inl q) = q := by
    intro q
    simp only [ret]
    rw [aeval_rename]
    have : (Sum.elim X 0 : (ι × Fin r) ⊕ ι → MvPolynomial (ι × Fin r) K) ∘ Sum.inl = X := by
      funext p; simp
    rw [this, aeval_X_left_apply]
  have := map_dvd ret hD'
  rwa [hDt, hT, ← rename_detLetters, hret, hret] at this
end Formalism.G0.DetDividesP
