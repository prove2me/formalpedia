-- Prove2me | solution 1 for CuspForm.mem_twoCuspIntegralSet_of_mem_twoCuspLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/88cca3eb-3844-57c2-836d-651880327020

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

namespace CuspForm
p2m_export "CuspForm" "translate ext coe_add twoCuspIntegralSet zero_mem_twoCuspIntegralSet twoCuspLattice exists_GammaH_coe_eq_alSlash"
namespace Eng1bH1
p2m_open "CuspForm"

open UpperHalfPlane

theorem unitsMap_eq_one_of_eq {n m₁ m₂ : ℕ} (h : m₁ = m₂) (h₁ : m₁ ∣ n) (h₂ : m₂ ∣ n) (u : (ZMod n)ˣ)
    (hu : ZMod.unitsMap h₂ u = 1) : ZMod.unitsMap h₁ u = 1 := by
  subst h; exact hu

theorem hHp_datum {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p ∣ M) {H : Subgroup (ZMod M)ˣ}
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) :
    ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
  have hR : M / p = W.R := Nat.div_eq_of_eq_mul_right hp.pos W.hM
  intro u hu
  exact hHp u (unitsMap_eq_one_of_eq hR _ _ u hu)

theorem T_mem_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
    simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.T]
  refine ⟨hT, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    simp [CongruenceSubgroup.Gamma0Map, ModularGroup.T]
  rw [h1]
  exact one_mem H

theorem one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem analyticAt_cuspFunction_one_gammaH (f : CuspForm (CohCarrier.GammaH M H) k) :
    AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_GammaH M H)

theorem qCoeff_add_of_coe_eq {u v : UpperHalfPlane → ℂ} (F G : CuspForm (CohCarrier.GammaH M H) k)
    (hu : ⇑F = u) (hv : ⇑G = v) (n : ℕ) :
    ModularFormClass.qCoeff (u + v) n = ModularFormClass.qCoeff u n + ModularFormClass.qCoeff v n := by
  subst hu hv
  unfold ModularFormClass.qCoeff
  rw [UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_one_gammaH F)
    (analyticAt_cuspFunction_one_gammaH G), map_add]

theorem qCoeff_smul_of_coe_eq {u : UpperHalfPlane → ℂ} (F : CuspForm (CohCarrier.GammaH M H) k)
    (hu : ⇑F = u) (c : ℂ) (n : ℕ) :
    ModularFormClass.qCoeff (c • u) n = c * ModularFormClass.qCoeff u n := by
  subst hu
  unfold ModularFormClass.qCoeff
  rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_one_gammaH F), map_smul, smul_eq_mul]

end CuspForm.Eng1bH1

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (y : CuspForm (CohCarrier.GammaH M H) 2) (hy : y ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    y ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
  have hp : p.Prime := Fact.out
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact CuspForm.zero_mem_twoCuspIntegralSet M H 2 p ⊥
  | add x x' _ _ hx hx' =>
      intro t ht W n
      have hHpW := CuspForm.Eng1bH1.hHp_datum hp hpM hHp W
      obtain ⟨gx, hgx⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHpW 2 (t x)
      obtain ⟨gx', hgx'⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHpW 2 (t x')
      obtain ⟨h1, h2⟩ := hx t ht W n
      obtain ⟨h1', h2'⟩ := hx' t ht W n
      refine ⟨?_, ?_⟩
      · rw [map_add, CuspForm.coe_add, CuspForm.Eng1bH1.qCoeff_add_of_coe_eq (t x) (t x') rfl rfl]
        exact add_mem h1 h1'
      · rw [map_add, CuspForm.coe_add, ModularForm.alSlash_add,
          CuspForm.Eng1bH1.qCoeff_add_of_coe_eq gx gx' hgx hgx']
        exact add_mem h2 h2'
  | smul a x _ hx =>
      intro t ht W n
      have hHpW := CuspForm.Eng1bH1.hHp_datum hp hpM hHp W
      obtain ⟨gx, hgx⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHpW 2 (t x)
      obtain ⟨h1, h2⟩ := hx t ht W n
      have hta : (⇑(t (a • x)) : UpperHalfPlane → ℂ) = (a : ℂ) • ⇑(t x) := by
        rw [Subring.smul_def, LinearMap.map_smul]; ext z; rfl
      refine ⟨?_, ?_⟩
      · rw [hta, CuspForm.Eng1bH1.qCoeff_smul_of_coe_eq (t x) rfl]
        exact mul_mem a.2 h1
      · rw [hta, ModularForm.alSlash_smul, CuspForm.Eng1bH1.qCoeff_smul_of_coe_eq gx hgx]
        exact mul_mem a.2 h2

end S_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice
end P2MW
export P2MW.S_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice (solution)
