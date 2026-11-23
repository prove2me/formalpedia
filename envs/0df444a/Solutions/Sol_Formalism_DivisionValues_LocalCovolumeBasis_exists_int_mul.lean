-- Prove2me | solution 1 for Formalism.DivisionValues.LocalCovolumeBasis.exists_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:40.992954+00:00
-- url     : https://prove2.me/submissions/47978a2d-d9ce-472d-ba48-2faf729b55f2

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues Formalism.DivisionValues.LocalCovolumeBasis
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.LocalCovolumeBasis
theorem _root_.solution {d : ℕ} (L : Submodule (𝓞 K) (Fin d → K))
    (hsp : Submodule.span K (L : Set (Fin d → K)) = ⊤) (e : Fin d → Fin d → K) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ i, ((y : K)) • e i ∈ L := by
  classical
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set (Fin d → K))
  have hfin : s.Finite := hli.setFinite
  haveI : Fintype s := hfin.fintype
  let f : Basis s K (Fin d → K) := Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  have hf : ∀ j, f j ∈ L := fun j => by rw [Basis.mk_apply]; exact hsL j.2
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun q : Fin d × s => f.repr (e q.1) q.2)
  refine ⟨y, hy, fun i => ?_⟩
  rw [← f.sum_repr (e i), Finset.smul_sum]
  apply Submodule.sum_mem
  intro j _
  have hi : IsIntegral ℤ (y • f.repr (e i) j) :=
    hint _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • f.repr (e i) j, hi⟩
  have hr : ((y : K)) • (f.repr (e i) j • f j) = r • f j := by
    rw [← algebraMap_smul K r, smul_smul]
    congr 1
    show (y : K) * f.repr (e i) j = y • f.repr (e i) j
    rw [zsmul_eq_mul]
  rw [hr]
  exact Submodule.smul_mem _ _ (hf j)
end Formalism.DivisionValues.LocalCovolumeBasis
