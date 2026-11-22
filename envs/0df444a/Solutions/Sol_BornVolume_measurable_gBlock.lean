-- Prove2me | solution 1 for BornVolume.measurable_gBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:04.882632+00:00
-- url     : https://prove2.me/submissions/988e6ac6-cf13-4302-b8c8-20ed91d89e64

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BornVolume
namespace BornVolume
theorem _root_.solution : Measurable gBlock := by unfold gBlock; fun_prop
end BornVolume
