-- Prove2me | solution 1 for Formalism.UG.P.exists_spherical_function_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:12.766316+00:00
-- url     : https://prove2.me/submissions/cabba3fd-4ecf-4fcc-9471-13c6683f521b

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Theorems.Thm_Formalism_UG_P_fIwasawa_chi_mul
import Theorems.Thm_Formalism_UG_P_fIwasawa_chi_int
import Theorems.Thm_Formalism_UG_P_fIwasawa_iwasawa
import Theorems.Thm_Formalism_UG_P_fIwasawa_wd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.SphericalExistsU := by
  intro L _ _ _ ϖ σ q n m hU hmn hnm α hα
  obtain ⟨hσ, hσv, -, -, -, hq2, -⟩ := hU
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  choose B K hB hK hBK using fIwasawa_iwasawa (n := n) σ hσ hσv
  have htri : ∀ g : GU σ n, IsBorelU g →
      (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    intro g hg i j hij
    exact hg i j hij
  have h1tri : (((1 : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    Matrix.blockTriangular_one
  refine ⟨fun g => chiDeltaU q α (B g), ?_, ?_, ?_⟩
  · intro b g k hb hk
    have e : b * g * k = (b * B g) * (K g * k) := by
      conv_lhs => rw [hBK g]
      simp only [mul_assoc]
    have hbB : (((b * B g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
      Matrix.BlockTriangular.mul (htri b hb) (htri _ (hB g))
    have hKk : K g * k ∈ KU σ n := (KU σ n).mul_mem (hK g) hk
    show chiDeltaU q α (B (b * g * k)) = chiDeltaU q α b * chiDeltaU q α (B g)
    rw [fIwasawa_wd σ q α hα hq (B (b * g * k)) (b * B g) (K (b * g * k)) (K g * k)
      (htri _ (hB _)) hbB (hK _) hKk (by rw [← hBK, e])]
    exact fIwasawa_chi_mul σ q α hα hq b (B g) (htri b hb) (htri _ (hB g))
  · show chiDeltaU q α (B 1) = 1
    rw [fIwasawa_wd σ q α hα hq (B 1) 1 (K 1) 1 (htri _ (hB 1)) h1tri (hK 1) (KU σ n).one_mem
      (by rw [← hBK, mul_one])]
    exact fIwasawa_chi_int σ q α 1 h1tri (KU σ n).one_mem
  · intro ψ hψ
    funext g
    have hg := hψ (B g) 1 (K g) (hB g) (hK g)
    rw [mul_one, ← hBK] at hg
    rw [hg]
    exact mul_comm _ _
end Formalism.UG.P
