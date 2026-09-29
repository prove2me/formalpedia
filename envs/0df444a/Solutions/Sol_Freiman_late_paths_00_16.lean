-- Prove2me | solution 1 for Freiman.late_paths_00_16
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T01:10:41.736999+00:00
-- url     : https://prove2.me/submissions/cdca2577-1f65-4d22-bbe1-dc2ac2eaebbd

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
   with block `latePathData1` alone. See the header comment of `gen_late_paths.py`
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

theorem hidx : ∀ i : ℕ, 0 ≤ i → i < 16 →
    lateCatalog.paths[i]? = latePathData1[i - 0]? := by
  intro i hlo hhi
  show (latePathData1 ++ latePathData2 ++ latePathData3 ++ latePathData4)[i]? = _
  rw [Array.getElem?_append_left (by rw [s3]; omega), Array.getElem?_append_left (by rw [s2]; omega), Array.getElem?_append_left (by rw [sD1]; omega)]; simp

abbrev pdflt : LatePath := ⟨false,[],[],[],[],[],[]⟩

theorem latePath_eq (i : ℕ) (h : 0 ≤ i) (h2 : i < 16) :
    latePath lateCatalog (i+1) = (latePathData1[i - 0]?).getD pdflt := by
  unfold latePath
  rw [Nat.add_sub_cancel, hidx i h h2]

theorem pathOK0 : latePathValid lateCatalog ((latePathData1[0]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK1 : latePathValid lateCatalog ((latePathData1[1]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK2 : latePathValid lateCatalog ((latePathData1[2]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK3 : latePathValid lateCatalog ((latePathData1[3]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK4 : latePathValid lateCatalog ((latePathData1[4]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK5 : latePathValid lateCatalog ((latePathData1[5]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK6 : latePathValid lateCatalog ((latePathData1[6]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK7 : latePathValid lateCatalog ((latePathData1[7]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK8 : latePathValid lateCatalog ((latePathData1[8]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK9 : latePathValid lateCatalog ((latePathData1[9]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK10 : latePathValid lateCatalog ((latePathData1[10]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK11 : latePathValid lateCatalog ((latePathData1[11]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK12 : latePathValid lateCatalog ((latePathData1[12]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK13 : latePathValid lateCatalog ((latePathData1[13]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK14 : latePathValid lateCatalog ((latePathData1[14]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem pathOK15 : latePathValid lateCatalog ((latePathData1[15]?).getD pdflt) := by
  unfold latePathValid lateIndices lateIndex
  decide +kernel

theorem solution : latePathBatch 0 16 := by
  intro i hlo hhi
  rw [latePath_eq i hlo hhi]
  have hj : i - 0 < 16 := by omega
  set j := i - 0 with hjdef
  interval_cases j <;> first
    | exact pathOK0 | exact pathOK1 | exact pathOK2 | exact pathOK3 | exact pathOK4 | exact pathOK5 | exact pathOK6 | exact pathOK7 | exact pathOK8 | exact pathOK9 | exact pathOK10 | exact pathOK11 | exact pathOK12 | exact pathOK13 | exact pathOK14 | exact pathOK15
