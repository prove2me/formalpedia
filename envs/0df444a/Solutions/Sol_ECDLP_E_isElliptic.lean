-- Prove2me | solution 1 for ECDLP.E_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:09:10.045427+00:00
-- url     : https://prove2.me/submissions/4941213a-8812-4698-851e-ccb6eeab864d

import Mathlib
import Definitions.Def_ECDLPChallengeData
set_option autoImplicit false
namespace ECDLP

theorem E_isElliptic : ECDLP.E.IsElliptic := by
  constructor
  refine IsUnit.of_mul_eq_one (b :=  (54038268503165619417957831988065987943890698540388741327815921983518953101034 : ZMod ECDLP.p)) ?_
  decide

end ECDLP

theorem solution : ECDLP.E.IsElliptic := ECDLP.E_isElliptic
