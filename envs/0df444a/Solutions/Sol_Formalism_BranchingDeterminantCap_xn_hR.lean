-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_hR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:47.369486+00:00
-- url     : https://prove2.me/submissions/ddb96b9b-3d56-4924-9545-2b1d9ef60e12

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_pderiv_supported
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_E_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {μ : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n μ)
    (t s : Fin n) (hts : t < s) : ∑ b : Fin r, X (b, t) * pderiv (b, s) f = 0 := by
  have hinv := (mem_dualWeyl_iff.1 hf).2 t s hts
  set ε : MvPolynomial (Option (Fin r × Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin n) ℂ :=
    aeval fun o => Option.elim o 0 X with hε
  have hεX : ∀ o, ε (X o) = Option.elim o 0 X := fun o => by rw [hε, aeval_X]
  have hεc : ∀ g, ε (colAddGen ℂ t s g) = g := by
    intro g
    have hc : ε.comp (colAddGen ℂ (r := r) t s) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply, AlgHom.id_apply, colAddGen, aeval_X]
      split_ifs <;> simp [hεX]
    simpa using AlgHom.congr_fun hc g
  have hXv : ∀ v : Fin r × Fin n, ε (pderiv none (colAddGen ℂ t s (X v))) =
      if v.2 = s then X (v.1, t) else 0 := by
    intro v
    simp only [colAddGen, aeval_X]
    split_ifs
    · simp [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hεX]
    · simp [MvPolynomial.pderiv_X, Pi.single_apply]
  have hE : ∀ v : Fin r × Fin n, ndE ℂ r n t s (X v) = if v.2 = s then X (v.1, t) else 0 :=
    fun v => by simp only [ndE, MvPolynomial.mkDerivation_X]
  have key : ∀ g, ε (pderiv none (colAddGen ℂ t s g)) = ndE ℂ r n t s g := by
    intro g
    induction g using MvPolynomial.induction_on
    next a => simp [MvPolynomial.derivation_C]
    next p q hp hq => simp only [map_add, hp, hq]
    next p v hp =>
      rw [map_mul (colAddGen ℂ (r := r) t s), Derivation.leibniz (pderiv (R := ℂ) none), smul_eq_mul,
        smul_eq_mul, map_add, map_mul ε, map_mul ε, hp, hεc, hεc, hXv,
        Derivation.leibniz (ndE ℂ r n t s), smul_eq_mul, smul_eq_mul, hE]
  have hsupp : rename (some : Fin r × Fin n → Option (Fin r × Fin n)) f ∈
      MvPolynomial.supported ℂ (Set.range (some : Fin r × Fin n → Option (Fin r × Fin n))) := by
    rw [MvPolynomial.mem_supported]
    intro o ho
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ ho)
    exact ⟨v, rfl⟩
  rw [xn_E_eq, ← key, hinv, xn_pderiv_supported _ none (by simp) _ hsupp, map_zero]
end Formalism.BranchingDeterminantCap
