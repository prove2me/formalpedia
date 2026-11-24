-- Prove2me | solution 1 for Formalism.UG.P.stabilizer_standard_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:25.797425+00:00
-- url     : https://prove2.me/submissions/2aa6ea30-8b2d-4e25-8b7c-b85347b73f94

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Theorems.Thm_Formalism_UG_P_map_mulVec_mem_stdLat
import Theorems.Thm_Formalism_UG_P_entries_mem_of_mem_stabGL
import Theorems.Thm_Formalism_UG_P_coe_bc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.StabStd := by
  intro A R _ _ _ n _ _ hinj
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ stabGL (stdLat (n := n) (A := A) R) := inv_mem hg
    choose r hr using entries_mem_of_mem_stabGL (R := R) g hg
    choose r' hr' using entries_mem_of_mem_stabGL (R := R) g⁻¹ hg'
    let M : Matrix n n R := Matrix.of r
    let M' : Matrix n n R := Matrix.of r'
    have hM : M.map (algebraMap R A) = (g : Matrix n n A) := by
      ext i j; simp [M, hr]
    have hM' : M'.map (algebraMap R A) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j; simp [M', hr']
    have h1 : M * M' = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.mul_inv g
    have h2 : M' * M = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.inv_mul g
    refine ⟨⟨M, M', h1, h2⟩, ?_⟩
    ext : 1
    rw [coe_bc]
    exact hM
  · rintro ⟨u, rfl⟩
    intro x
    constructor
    · intro hx
      rw [coe_bc]
      exact map_mulVec_mem_stdLat _ x hx
    · intro hx
      have hinv := map_mulVec_mem_stdLat (A := A) ((u⁻¹ : GL n R) : Matrix n n R) _ hx
      rw [← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Matrix.one_mulVec] at hinv
      exact hinv
end Formalism.UG.P
