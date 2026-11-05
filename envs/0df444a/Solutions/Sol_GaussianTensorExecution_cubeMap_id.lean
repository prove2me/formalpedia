-- Prove2me | solution 1 for GaussianTensorExecution.cubeMap_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/ab42fc85-ae96-4866-b41f-5dd0196a2afb

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cube_ext
import Theorems.Thm_GaussianTensorExecution_get_map

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (z : Cube n) : cubeMap (fun u => u) n z = z := by
  apply cube_ext n
  intro p
  rw [get_map]
end GaussianTensorExecution
