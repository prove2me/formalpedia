-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.length_quot_map_positionMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:03.284547+00:00
-- url     : https://prove2.me/submissions/022596e4-efb6-4d36-a2af-f36cf4a920c1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_length_quot_map_of_injective
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_length_quot_pi_const
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_factorMap_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
variable {K : Type*} [Field K]
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ))
    (O : Subring K) (A₀ B₀ : Submodule O (MvPolynomial σ K)) :
    Module.length O (((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
          ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)) ⧸
        ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => B₀).map ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).comap
          ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
            ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) • Module.length O (A₀ ⧸ B₀.comap A₀.subtype) := by
  rw [length_quot_map_of_injective _ (show Function.Injective ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) from
    factorMap_injective τ₀ κ b hb), length_quot_pi_const, Fintype.card_pi]
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
