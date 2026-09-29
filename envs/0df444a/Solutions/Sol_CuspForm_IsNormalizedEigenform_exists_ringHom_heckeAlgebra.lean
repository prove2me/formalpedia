-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/79f7e296-2496-5d5d-8c39-92a471017a8a

import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra

noncomputable section

open ModularForm ModularFormClass

namespace FrobChareqC2

variable {N : ℕ} {k : ℤ}

theorem hΓ (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

theorem qCoeff_add (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff ⇑(f + g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  simp only [qCoeff, CuspForm.coe_add]
  rw [ModularForm.qExpansion_add one_pos (hΓ N) f g, map_add]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  have h1 : ⇑(c • f) = c • ⇑f := by ext z; simp
  simp only [qCoeff, h1]
  rw [ModularForm.qExpansion_smul one_pos (hΓ N) c f]
  simp

end FrobChareqC2

p2m_open "P2MW.S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra.FrobChareqC2 CuspForm ModularForm.CuspForm"

namespace FrobChareqC2

def eigenChar {N : ℕ} [NeZero N] (S : Set ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    heckeAlgebra N 2 S → ℂ := fun t =>
  qCoeff ((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f) 1

theorem eigen_of_mem {N : ℕ} [NeZero N] {S : Set ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)}
    (ht : t ∈ heckeAlgebra N 2 S) : t f = (qCoeff ⇑(t f) 1) • f := by
  have h1 : qCoeff ⇑f 1 = 1 := hf.qCoeff_one
  have hgen := (CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf
  refine Algebra.adjoin_induction
    (p := fun (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) _ =>
      t f = (qCoeff ⇑(t f) 1) • f) ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩)
    · have h := (hgen.2 ℓ hℓ).1 hℓN
      rw [h, qCoeff_smul, h1, mul_one]
    · have h := (hgen.2 q hq).2 hqN
      rw [h, qCoeff_smul, h1, mul_one]
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      ← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, h1, mul_one]
  · intro x y _ _ hx hy
    rw [LinearMap.add_apply, qCoeff_add, add_smul, ← hx, ← hy]
  · intro x y _ _ hx hy
    rw [Module.End.mul_apply, hy, map_smul, hx, smul_smul, qCoeff_smul, h1, mul_one]

end FrobChareqC2

theorem solution {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (S : Set ℕ) : ∃ χ : CuspForm.heckeAlgebra N 2 S →+* ℂ, (∀ t : CuspForm.heckeAlgebra N 2 S, (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = χ t • f) ∧ (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = ModularFormClass.qCoeff f ℓ) ∧ ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S), χ (CuspForm.heckeAlgebra.U hq hqN hqS) = ModularFormClass.qCoeff f q := by
  have h1 : qCoeff ⇑f 1 = 1 := hf.qCoeff_one
  have hgen := (CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf
  have key : ∀ t : heckeAlgebra N 2 S,
      (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = eigenChar S f t • f :=
    fun t => eigen_of_mem hf t.2
  let χ : heckeAlgebra N 2 S →+* ℂ :=
    { toFun := eigenChar S f
      map_one' := by
        show qCoeff ⇑((1 : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f) 1 = 1
        rw [Module.End.one_apply, h1]
      map_mul' := fun t t' => by
        show qCoeff ⇑(((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) * (t' : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) f) 1 = eigenChar S f t * eigenChar S f t'
        rw [Module.End.mul_apply, key t', map_smul, key t, smul_smul, qCoeff_smul, h1, mul_one, mul_comm]
      map_zero' := by
        show qCoeff ⇑((0 : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f) 1 = 0
        rw [LinearMap.zero_apply]
        have := qCoeff_smul (0 : ℂ) f 1
        rw [zero_smul, zero_mul] at this
        exact this
      map_add' := fun t t' => by
        show qCoeff ⇑(((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) + (t' : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) f) 1 = eigenChar S f t + eigenChar S f t'
        rw [LinearMap.add_apply, qCoeff_add]
        rfl }
  refine ⟨χ, key, fun ℓ hℓ hℓN hℓS => ?_, fun q hq hqN hqS => ?_⟩
  · show qCoeff ⇑((CuspForm.heckeTLin 2 hℓ hℓN) f) 1 = qCoeff ⇑f ℓ
    rw [(hgen.2 ℓ hℓ).1 hℓN, qCoeff_smul, h1, mul_one]
  · show qCoeff ⇑((CuspForm.heckeULin 2 hqN) f) 1 = qCoeff ⇑f q
    rw [(hgen.2 q hq).2 hqN, qCoeff_smul, h1, mul_one]

end

end S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra (solution)
