-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.psi_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:00:51.71021+00:00
-- url     : https://prove2.me/submissions/f0cda665-1183-4593-a2a3-82b394e91a45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_sec
import Theorems.Thm_Formalism_L2_Pj_GenSect_sub_incl_psi_mem

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
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    psi x j₀ f = 0 ↔ f ∈ Ideal.span (Set.range (sec x)) := by
  constructor
  · intro h
    have hm := sub_incl_psi_mem x j₀ hx₀ f
    rwa [h, map_zero, sub_zero] at hm
  · intro hf
    have hle : Ideal.span (Set.range (sec (D := D) x)) ≤ RingHom.ker (psi (D := D) x j₀) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (psi_sec x j₀ hx₀ i)
    exact RingHom.mem_ker.mp (hle hf)
end Formalism.L2.Pj.GenSect
