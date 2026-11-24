-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.theta_dot_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:45.777897+00:00
-- url     : https://prove2.me/submissions/738a316a-8899-4226-a2f1-64f14e66e30a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ThetaDotSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
private lemma rho_dot_self_lemma {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (w : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ j, Complex.normSq (w i j) := by
  unfold rho
  simp only [dotProduct]
  refine (Equiv.sum_comp eqv (fun x : ι × Fin r × Fin 2 =>
    (if x.2.2 = 0 then (w x.1 x.2.1).re else (w x.1 x.2.1).im) *
      (if x.2.2 = 0 then (w x.1 x.2.1).re else (w x.1 x.2.1).im))).trans ?_
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
end Formalism.L2.Pj.FundamentalDomainD5
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution (p : ℕ) {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (w : ι → Fin r → ℂ) :
    rho eqv (Theta p w) ⬝ᵥ rho eqv (Theta p w) = rho eqv w ⬝ᵥ rho eqv w := by
  rw [rho_dot_self_lemma, rho_dot_self_lemma]
  unfold Theta sgn
  simp only [map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp
end Formalism.L2.Pj.FundamentalDomainD5
