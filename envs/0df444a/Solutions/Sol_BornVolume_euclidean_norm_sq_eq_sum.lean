-- Prove2me | solution 1 for BornVolume.euclidean_norm_sq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:24.364989+00:00
-- url     : https://prove2.me/submissions/81e64cea-e534-4700-8894-1fa1d8f6944d

module
public import Definitions.Def_BornVolumeLean_Volume_CPN
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
public import Definitions.Def_BornVolumeLean_Volume_MomentMap

set_option autoImplicit false
@[expose] public section
public section
open scoped LinearAlgebra.Projectivization
open BornVolume
namespace BornVolume
theorem _root_.solution {N : ℕ} (v : EuclideanSpace ℂ (Fin N)) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq v
end BornVolume
