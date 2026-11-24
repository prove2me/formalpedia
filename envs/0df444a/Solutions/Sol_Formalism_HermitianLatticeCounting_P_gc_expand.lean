-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gc_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:22.438131+00:00
-- url     : https://prove2.me/submissions/7c1e0222-c34d-4b7f-a405-88e78fd7c28c

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {l : ℕ} (y : Fin l → V) (a : Fin l) :
    y a = ∑ b, gramSchmidtUnitriangularMatrix y a b • gramSchmidt ℂ y b := by
  conv_lhs => rw [gramSchmidt_def'' ℂ y a]
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ a)]
  congr 1
  · simp [gramSchmidtUnitriangularMatrix]
  · symm
    rw [← Finset.sum_subset (s₁ := Iio a)]
    · refine Finset.sum_congr rfl fun b hb => ?_
      have hb' : b < a := Finset.mem_Iio.1 hb
      simp [gramSchmidtUnitriangularMatrix, hb', hb'.ne]
    · intro b hb
      have hb' : b < a := Finset.mem_Iio.1 hb
      simp [hb'.ne]
    · intro b hb hb2
      have h1 : b ≠ a := by simpa using hb
      have h2 : ¬ b < a := by simpa using hb2
      simp [gramSchmidtUnitriangularMatrix, h1, h2]
end Formalism.HermitianLatticeCounting.P
