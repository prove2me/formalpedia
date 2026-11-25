-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.ker_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:12:52.167241+00:00
-- url     : https://prove2.me/submissions/ec2dcba9-cb92-4995-a2cc-260ad8849487

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
import Theorems.Thm_Formalism_L2_Pj_GenSect_Phi_algebraMap
import Theorems.Thm_P2M_Formalism_L2_Pj_GenSect_Phi_mk__spec_b1aeb19d49e4
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_eq_zero_iff
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_sec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    Is K x = RingHom.ker (Phi x j₀ hinj) := by
  apply le_antisymm
  · rw [Is, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, Phi_algebraMap, psi_sec x j₀ hx₀ i, map_zero]
  · intro r hr
    rw [RingHom.mem_ker] at hr
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only at hr ⊢
    rw [Phi_mk'_spec, mul_zero, ← map_zero (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))),
      (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).eq_iff,
      psi_eq_zero_iff x j₀ hx₀] at hr
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    apply Ideal.mul_mem_right
    have hle : Ideal.map (algebraMap (ΩT Ω D m) (RS K Ω D m)) (Ideal.span (Set.range (sec x))) ≤ Is K x := by
      rw [Ideal.map_span, Is]
      apply Ideal.span_mono
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    exact hle (Ideal.mem_map_of_mem _ hr)
end Formalism.L2.Pj.GenSect
