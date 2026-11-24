-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.wal_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:24:45.729842+00:00
-- url     : https://prove2.me/submissions/77142e08-b44d-4740-a528-b1fc33e52fe9

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_upper
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_lower
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
local notation "Av" => E ⊗[F] v.adicCompletion F
local notation "Sv" => Formalism.UG.P.lvS F E v
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ N : Matrix n n Av, walInt Sv N →
      ∀ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ,
        ((m : Av) • N) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ := by
  obtain ⟨m₁, h₁, hu⟩ := wal_upper v Λ hfin
  obtain ⟨m₂, h₂, hl⟩ := wal_lower v Λ hspan
  refine ⟨m₂ * m₁, mul_ne_zero h₂ h₁, fun N hN x hx => ?_⟩
  have : (((m₂ * m₁ : ℤ) : Av) • N) *ᵥ x =
      fun i => (m₂ : Av) * ∑ j, N i j * ((m₁ : Av) * x j) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      Int.cast_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  exact hl _ fun i => Subring.sum_mem _ fun j _ => mul_mem (hN i j) (hu x hx j)
end Formalism.MainNotions.Gaps.CC.Surj
