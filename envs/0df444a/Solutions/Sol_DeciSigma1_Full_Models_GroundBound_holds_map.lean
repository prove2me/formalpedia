-- Prove2me | solution 1 for DeciSigma1.Full.Models.GroundBound.holds_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:23.147059+00:00
-- url     : https://prove2.me/submissions/bc8f76c3-52bd-4eda-b8a1-1a02c0bb7fde

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Full.Models
namespace GroundBound
theorem _root_.solution {V W : Type*} (f : V → W)
    (b : GroundBound n V) (ρ : W → Semantics.Tree n) :
    (b.map f).Holds ρ ↔ b.Holds (ρ ∘ f) := Iff.rfl
end GroundBound
end DeciSigma1.Full.Models
