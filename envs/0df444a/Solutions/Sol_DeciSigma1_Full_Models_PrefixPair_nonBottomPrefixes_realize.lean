-- Prove2me | solution 1 for DeciSigma1.Full.Models.PrefixPair.nonBottomPrefixes_realize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:36:20.499541+00:00
-- url     : https://prove2.me/submissions/241329ee-3678-4041-861b-58d715ef914d

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_realize_observations

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
attribute [local instance] Classical.propDecidable
namespace DeciSigma1.Full.Models
namespace PrefixPair
theorem _root_.solution (p : PrefixPair n) :
    nonBottomPrefixes (PrefixPair.realize p) = p.nonBottom := by
  ext w; exact (PrefixPair.realize_observations p w).1
end PrefixPair
end DeciSigma1.Full.Models
