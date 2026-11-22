-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic_locS_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:03.608585+00:00
-- url     : https://prove2.me/submissions/70d35f2e-c213-41fc-974c-7368c330b1fa

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (Y : Submodule R V) (hY : Submodule.span K (Y : Set V) = ⊤) :
    locS (nonZeroDivisors R) Y = ⊤ := by
  let T : Submodule K V :=
    { carrier := locS (nonZeroDivisors R) Y
      add_mem' := (locS (nonZeroDivisors R) Y).add_mem
      zero_mem' := (locS (nonZeroDivisors R) Y).zero_mem
      smul_mem' := by
        rintro c v ⟨d, hd, hdv⟩
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R c
        have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        refine ⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩
        have hc : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
          field_simp
        have : (b * d) • ((algebraMap R K a / algebraMap R K b) • v) = a • (d • v) := by
          rw [mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul,
            smul_comm]
        rw [this]
        exact Y.smul_mem a hdv }
  have hle : Submodule.span K (Y : Set V) ≤ T :=
    Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)
  rw [hY] at hle
  exact eq_top_iff.mpr (fun v _ => hle Submodule.mem_top)
end Formalism.HermitianLatticesTheory
