-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.dualLattice_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:05.910246+00:00
-- url     : https://prove2.me/submissions/ece26506-f798-4562-83ed-db24b5bb88a6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice

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
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : h.Nondegenerate) (b : Basis ι K V) (bs : ι → V)
    (hbs : ∀ i j, h (b i) (bs j) = if i = j then 1 else 0) (x : V) :
    x = ∑ j, h (b j) x • bs j := by
  classical
  set z := x - ∑ j, h (b j) x • bs j with hzdef
  have hz : ∀ i, h (b i) z = 0 := by
    intro i
    simp [z, map_sub, map_sum, map_smul, hbs, smul_eq_mul]
  have hflip : h.flip z = 0 := b.ext fun i => by simp [hz i]
  have hz0 : z = 0 := hnd.2 z fun y => by simpa using LinearMap.congr_fun hflip y
  exact sub_eq_zero.mp hz0
end Formalism.HermitianLatticesTheory
