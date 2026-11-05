-- Prove2me | solution 1 for GaussianTensorExecution.inverse_forward_leaf_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/6a415445-e9db-4cfd-af99-fcdce2a74418

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_inverse_forward_leaf_sameValue
import Theorems.Thm_GaussianSynthesis_normalize_congr


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n e : Nat) (z : Cube n) (p : Path n) :
    normalize ⟨get n (inverse n (forward n z)) p,e+2*n⟩ = normalize ⟨get n z p,e⟩ :=
  normalize_congr (inverse_forward_leaf_sameValue n e z p)
end GaussianTensorExecution
