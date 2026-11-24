-- Prove2me | solution 1 for Formalism.UG.P.levelv_smul_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:59.445349+00:00
-- url     : https://prove2.me/submissions/c62a3536-5e91-4916-9cf0-0ef8299a4a43

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_mem_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (N : ℕ) (M : Matrix n n (E ⊗[F] v.adicCompletion F))
    (hM : ∀ i j, N • M i j ∈ lvS F E v) (x : n → E ⊗[F] v.adicCompletion F)
    (hx : x ∈ stdLat (n := n) ↥(lvS F E v)) :
    N • (M *ᵥ x) ∈ stdLat (n := n) ↥(lvS F E v) := by
  rw [levelv_mem_lat] at hx ⊢
  intro i
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  rw [← smul_mul_assoc]
  exact mul_mem (hM i j) (hx j)
end Formalism.UG.P
