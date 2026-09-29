-- Prove2me | solution 1 for FLT.ModelTransfer.reducedChange_smul_reductionMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6ca4df24-cc12-5538-b462-a6be5eec1482

import Definitions.Def_ModelTransfer_ClearedData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_ModelTransfer_reducedChange_smul_reductionMod

open WeierstrassCurve FLT.ModelTransfer

theorem solution {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ}
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : FLT.ModelTransfer.ClearedData C) {q : ℕ} [Fact q.Prime] (hq : ¬ q ∣ D.N) :
    (FLT.ModelTransfer.reducedChange D hq) • (V.reductionMod q) = W.reductionMod q := by
  have hN : ((D.N : ZMod q)) ≠ 0 := N_ne_zero_zmod D hq
  have key₁ := congrArg (fun m : ℤ => ((m : ZMod q))) (intId₁ hC D)
  have key₂ := congrArg (fun m : ℤ => ((m : ZMod q))) (intId₂ hC D)
  have key₃ := congrArg (fun m : ℤ => ((m : ZMod q))) (intId₃ hC D)
  have key₄ := congrArg (fun m : ℤ => ((m : ZMod q))) (intId₄ hC D)
  have key₆ := congrArg (fun m : ℤ => ((m : ZMod q))) (intId₆ hC D)
  push_cast at key₁ key₂ key₃ key₄ key₆
  have hext : ∀ X Y : WeierstrassCurve (ZMod q), X.a₁ = Y.a₁ → X.a₂ = Y.a₂ → X.a₃ = Y.a₃ →
      X.a₄ = Y.a₄ → X.a₆ = Y.a₆ → X = Y := by
    rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ rfl rfl rfl rfl rfl
    rfl
  apply hext
  · show ((((reducedChange D hq).u)⁻¹ : (ZMod q)ˣ) : ZMod q)
        * ((V.reductionMod q).a₁ + 2 * (reducedChange D hq).s) = (W.reductionMod q).a₁
    simp only [reducedChange_u_inv, reducedChange_s, reductionMod, map_a₁, eq_intCast]
    field_simp
    linear_combination -key₁
  · show ((((reducedChange D hq).u)⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2
        * ((V.reductionMod q).a₂ - (reducedChange D hq).s * (V.reductionMod q).a₁
          + 3 * (reducedChange D hq).r - (reducedChange D hq).s ^ 2)
        = (W.reductionMod q).a₂
    simp only [reducedChange_u_inv, reducedChange_s, reducedChange_r, reductionMod, map_a₁,
      map_a₂, eq_intCast]
    field_simp
    linear_combination -key₂
  · show ((((reducedChange D hq).u)⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 3
        * ((V.reductionMod q).a₃ + (reducedChange D hq).r * (V.reductionMod q).a₁
          + 2 * (reducedChange D hq).t)
        = (W.reductionMod q).a₃
    simp only [reducedChange_u_inv, reducedChange_r, reducedChange_t, reductionMod, map_a₁,
      map_a₃, eq_intCast]
    field_simp
    linear_combination -key₃
  · show ((((reducedChange D hq).u)⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 4
        * ((V.reductionMod q).a₄ - (reducedChange D hq).s * (V.reductionMod q).a₃
          + 2 * (reducedChange D hq).r * (V.reductionMod q).a₂
          - ((reducedChange D hq).t + (reducedChange D hq).r * (reducedChange D hq).s)
            * (V.reductionMod q).a₁
          + 3 * (reducedChange D hq).r ^ 2
          - 2 * (reducedChange D hq).s * (reducedChange D hq).t)
        = (W.reductionMod q).a₄
    simp only [reducedChange_u_inv, reducedChange_s, reducedChange_r, reducedChange_t,
      reductionMod, map_a₁, map_a₂, map_a₃, map_a₄, eq_intCast]
    field_simp
    linear_combination -key₄
  · show ((((reducedChange D hq).u)⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 6
        * ((V.reductionMod q).a₆ + (reducedChange D hq).r * (V.reductionMod q).a₄
          + (reducedChange D hq).r ^ 2 * (V.reductionMod q).a₂ + (reducedChange D hq).r ^ 3
          - (reducedChange D hq).t * (V.reductionMod q).a₃ - (reducedChange D hq).t ^ 2
          - (reducedChange D hq).r * (reducedChange D hq).t * (V.reductionMod q).a₁)
        = (W.reductionMod q).a₆
    simp only [reducedChange_u_inv, reducedChange_r, reducedChange_t, reductionMod, map_a₁,
      map_a₂, map_a₃, map_a₄, map_a₆, eq_intCast]
    field_simp
    linear_combination -key₆

end S_FLT_ModelTransfer_reducedChange_smul_reductionMod
end P2MW
export P2MW.S_FLT_ModelTransfer_reducedChange_smul_reductionMod (solution)
