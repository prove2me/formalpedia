-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.prod_mul_le_detIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:42.919086+00:00
-- url     : https://prove2.me/submissions/991fb88e-2052-4090-9ad4-112182e209b3

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_Formalism_L2_LamCM_A2_detSub_isFractional
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_coe
import Theorems.Thm_Formalism_L2_LamCM_A2_det_mem
import Theorems.Thm_Formalism_L2_LamCM_A2_coe_prod_fi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {m : ℕ} (L : MLat K m) (hL : L.Good) (ℓ : Fin m → MLine K)
    (u : Fin m → Fin m → K) (hu : ∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ L.M) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of u).det ≤ L.detIdeal := by
  rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
    detIdeal_coe L (detSub_isFractional L hL.1), coe_prod_fi, Submodule.mul_le]
  intro p hp q hq
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq
  rw [mul_smul_comm]
  apply Submodule.smul_mem
  have hspan : ∏ j, ((ℓ j).I : Submodule (𝓞 K) K) =
      Submodule.span (𝓞 K) (∏ j, (((ℓ j).I : Submodule (𝓞 K) K) : Set K)) := by
    rw [← Submodule.prod_span]
    simp only [Submodule.span_eq]
  rw [hspan] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hp
    have : (∏ j, g j) * (Matrix.of u).det = (Matrix.of fun j k => g j * u j k).det := by
      exact (Matrix.det_mul_column g (Matrix.of u)).symm
    rw [this]
    exact det_mem L _ fun j => by
      have := hu j (g j) (hg (Finset.mem_univ j))
      simpa [Pi.smul_def, smul_eq_mul] using this
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
end Formalism.L2.LamCM.A2
