-- Prove2me | solution 1 for Formalism.L2.DIV.transLat_gLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:32.644604+00:00
-- url     : https://prove2.me/submissions/db4b4aa3-0dda-48eb-ad1c-e8f9505a9d7f

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_polyAction_mul
import Theorems.Thm_P2M_Formalism_L2_DIV_polyAction_one__f4d3cf3e4198
import Theorems.Thm_Formalism_L2_DIV_mem_transLat_gLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) :
    transLat lam T (fun τ => gLat (g τ) (M τ)) = (transLat lam T M).map ((actP lam g).restrictScalars (𝓞 K)) := by
  ext F
  rw [mem_transLat_gLat, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    show actP lam g (actP lam g⁻¹ F) = F
    rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  · rintro ⟨y, hy, rfl⟩
    show actP lam g⁻¹ (actP lam g y) ∈ _
    rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
    exact hy
end Formalism.L2.DIV
