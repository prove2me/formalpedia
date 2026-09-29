-- Prove2me | solution 1 for Freiman.late_paths_48_63
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T01:11:38.144184+00:00
-- url     : https://prove2.me/submissions/c7cb69a6-0036-4623-97db-76249d90c537

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

open Freiman
set_option linter.all false

/- ===================================================================
   `lateCatalog.paths` is the concatenation
   `latePathData1 ++ latePathData2 ++ latePathData3 ++ latePathData4`
   (sizes 16,16,16,15 = 63). This leaf's global range coincides exactly
   with block `latePathData4` alone. See the header comment of `gen_late_paths.py`
   for the two `Decidable`-synthesis fixes this family needed (a custom
   instance for `lateCheckValid`'s internal `match`, plus a larger
   `synthInstance.maxSize`). No Bernstein/CertField arithmetic anywhere
   in this family, so each path is cheap (~2-4s) -- every path gets its
   own top-level theorem via direct array indexing so the kernel can
   check them in parallel.
   =================================================================== -/

instance decLateCheckValid (C : LateCatalog) (p : LatePath) (c : LateCheck) :
    Decidable (lateCheckValid C p c) := by
  unfold lateCheckValid lateIndex
  rcases lateGreater (lateEndpoint C c.a).value (lateEndpoint C c.b).value c.strict with
    _ | _ | b <;> infer_instance

theorem sD1 : latePathData1.size = 16 := by decide
theorem sD2 : latePathData2.size = 16 := by decide
theorem sD3 : latePathData3.size = 16 := by decide
theorem sD4 : latePathData4.size = 15 := by decide

theorem s2 : (latePathData1 ++ latePathData2).size = 32 := by
  rw [Array.size_append, sD1, sD2]
theorem s3 : (latePathData1 ++ latePathData2 ++ latePathData3).size = 48 := by
  rw [Array.size_append, s2, sD3]
theorem s4 : (latePathData1 ++ latePathData2 ++ latePathData3 ++ latePathData4).size = 63 := by
  rw [Array.size_append, s3, sD4]

theorem hidx : ∀ i : ℕ, 48 ≤ i → i < 63 →
    lateCatalog.paths[i]? = latePathData4[i - 48]? := by
  intro i hlo hhi
  show (latePathData1 ++ latePathData2 ++ latePathData3 ++ latePathData4)[i]? = _
  rw [Array.getElem?_append_right (by rw [s3]; omega), s3]

abbrev pdflt : LatePath := ⟨false,[],[],[],[],[],[]⟩

theorem latePath_eq (i : ℕ) (h : 48 ≤ i) (h2 : i < 63) :
    latePath lateCatalog (i+1) = (latePathData4[i - 48]?).getD pdflt := by
  unfold latePath
  rw [Nat.add_sub_cancel, hidx i h h2]

theorem pathOK0 : latePathValid lateCatalog ((latePathData4[0]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK1 : latePathValid lateCatalog ((latePathData4[1]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK2 : latePathValid lateCatalog ((latePathData4[2]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK3 : latePathValid lateCatalog ((latePathData4[3]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK4 : latePathValid lateCatalog ((latePathData4[4]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK5 : latePathValid lateCatalog ((latePathData4[5]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK6 : latePathValid lateCatalog ((latePathData4[6]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK7 : latePathValid lateCatalog ((latePathData4[7]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK8 : latePathValid lateCatalog ((latePathData4[8]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK9 : latePathValid lateCatalog ((latePathData4[9]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK10 : latePathValid lateCatalog ((latePathData4[10]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK11 : latePathValid lateCatalog ((latePathData4[11]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK12 : latePathValid lateCatalog ((latePathData4[12]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK13 : latePathValid lateCatalog ((latePathData4[13]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK14 : latePathValid lateCatalog ((latePathData4[14]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem solution : latePathBatch 48 63 := by
  intro i hlo hhi
  rw [latePath_eq i hlo hhi]
  have hj : i - 48 < 15 := by omega
  set j := i - 48 with hjdef
  interval_cases j <;> first
    | exact pathOK0 | exact pathOK1 | exact pathOK2 | exact pathOK3 | exact pathOK4 | exact pathOK5 | exact pathOK6 | exact pathOK7 | exact pathOK8 | exact pathOK9 | exact pathOK10 | exact pathOK11 | exact pathOK12 | exact pathOK13 | exact pathOK14
