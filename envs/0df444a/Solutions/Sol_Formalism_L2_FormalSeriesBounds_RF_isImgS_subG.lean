-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.isImgS_subG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:41:38.807923+00:00
-- url     : https://prove2.me/submissions/b6ca55d3-e9e5-489d-ac38-1e93def028ad

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_mem_vars_subG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_coS_off
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_back_subG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_gram_matrix_mul_left
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_sum_coS
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {dd : ℕ} (X : ∀ o, RawChart C 2 (fun _ => IIs r tau o) (Fin 2 × Fin dd))
    (uv : Letter T r n → Fin dd → C) (e : ∀ o, IIs r tau o → Fin dd → C)
    (hu : ∀ o g (c : IIs r tau o) x, (X o).u g c x = gm o c.1 x.1 g * e o c x.2)
    (huv : ∀ o (c : IIs r tau o) b, uv ⟨tau o c.1, c.2, b⟩ = e o c)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    IsImgS X plc (fun ℓ : Letter T r n => ℓ.2.2) uv (subG r tau gm plc Q) Q := by
  refine ⟨coS r tau gm plc, ?_, (back_subG plc inj gm_hyp Q).symm⟩
  intro ℓ hℓ
  obtain ⟨⟨α, col⟩, rfl⟩ := mem_vars_subG plc hℓ
  refine ⟨α.1, col, rfl, fun ρ' w h => coS_off plc inj α col (ρ', w) h, ?_⟩
  have h1 : (∑ w : (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) (α.1, w) •
      (X w.1).u w.2.1 w.2.2) =
      ∑ y : Fin N × (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) y •
        (X y.2.1).u y.2.2.1 y.2.2.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single α.1]
    · intro ρ' _ hne
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [coS_off plc inj α col (ρ', w) hne, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, sum_coS plc inj α col (fun c y => c • (X y.2.1).u y.2.2.1 y.2.2.2) (fun y => zero_smul _ _)]
  funext x
  rw [Finset.sum_apply]
  have h2 : ∀ g, (Mm r tau gm α col g • (X ((eW r tau N).symm (α, g)).2.1).u ((eW r tau N).symm (α, g)).2.2.1
      ((eW r tau N).symm (α, g)).2.2.2) x = (Gm r tau gm α x.1 g * Mm r tau gm α col g) * e α.2.1 α.2.2 x.2 := by
    intro g
    rw [Pi.smul_apply, smul_eq_mul]
    show Mm r tau gm α col g * (X α.2.1).u g α.2.2 x = _
    rw [hu]
    unfold Gm
    ring
  simp only [h2]
  rw [← Finset.sum_mul, gram_matrix_mul_left gm_hyp α col x.1]
  have h3 : uv (lam r tau plc (α, col)) = e α.2.1 α.2.2 := huv α.2.1 α.2.2 _
  rw [h3]
  split_ifs <;> simp
end Formalism.L2.FormalSeriesBounds.RF
