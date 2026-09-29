-- Prove2me | solution 1 for FamousTheorems.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:46.681403+00:00
-- url     : https://prove2.me/submissions/9374113f-b642-4a9a-9471-fddc9432310e

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) 
    {x₁ x₂ y z : V}, 
    x₁ ≠ y → 
    x₁ ≠ z → 
    x₂ ≠ y → 
    x₂ ≠ z → 
    ∀ {r : ℝ}, 
    ‖x₁‖ = r → ‖x₂‖ = r → ‖y‖ = r → ‖z‖ = r → 2 • o.oangle (y - x₁) (z - x₁) = 2 • o.oangle (y - x₂) (z - x₂) :=
  @_root_.Orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
