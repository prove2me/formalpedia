-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:51.832135+00:00
-- url     : https://prove2.me/submissions/de81963d-5a12-464a-a294-7b53fa84faff

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic

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
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [IsNoetherianRing R] [Ring.KrullDimLE 1 R] {d : R}
    (hd : d ∈ nonZeroDivisors R) (s : R) :
    ∃ n : ℕ, ∃ t : R, ∃ u : R, s ^ n - s ^ (n + 1) * t = d * u := by
  have hfl : IsFiniteLength R (R ⧸ Ideal.span {d}) := isFiniteLength_quotient_span_singleton R hd
  have hart : IsArtinian R (R ⧸ Ideal.span {d}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd s (1 : R ⧸ Ideal.span {d})
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hy' : Ideal.Quotient.mk (Ideal.span {d}) (s ^ (n + 1) * t) =
      Ideal.Quotient.mk (Ideal.span {d}) (s ^ n) := by
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hy
  have : Ideal.Quotient.mk (Ideal.span {d}) (s ^ n - s ^ (n + 1) * t) = 0 := by
    rw [map_sub, hy', sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at this
  obtain ⟨u, hu⟩ := this
  exact ⟨n, t, u, by rw [← hu, mul_comm]⟩
end Formalism.HermitianLatticesTheory
