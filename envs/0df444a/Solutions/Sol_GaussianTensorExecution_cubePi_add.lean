-- Prove2me | solution 1 for GaussianTensorExecution.cubePi_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/82f981fb-ac0d-4cd1-9e76-5ef45953a14f

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cubeMap_zip
import Theorems.Thm_GaussianTensorExecution_mulPi_add

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (u v : Cube n) :
    cubePi n (cubeAdd n u v) = cubeAdd n (cubePi n u) (cubePi n v) := by
  exact cubeMap_zip n mulPi add mulPi_add u v
end GaussianTensorExecution
