-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.low_subst_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.367463+00:00
-- url     : https://prove2.me/submissions/156554df-c0c3-4d55-b966-50ec95358abb

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mul
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_sum
import Theorems.Thm_Formalism_FG_InvIntVAux_low_one
import Theorems.Thm_Formalism_FG_InvIntVAux_low_of_agree
import Theorems.Thm_Formalism_FG_InvIntVAux_decomp
import Theorems.Thm_Formalism_G_LogCR_Agree_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
universe u v w
namespace Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
section Basic
variable {σ : Type*}
end Basic
private theorem subst_diff_lemma {σ τ : Type*} [Fintype σ] [Finite τ] (N : ℕ) :
    ∀ (z : MvPowerSeries σ K) (a b : σ → MvPowerSeries τ K),
      (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
      (∀ i, MvPowerSeries.constantCoeff (b i) = 0) → (∀ i, Agree N (a i) (b i)) →
      Low N (MvPowerSeries.subst a z - MvPowerSeries.subst b z) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  induction N with
  | zero => intro z a b _ _ _ d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ N ih =>
    intro z a b ha hb hab
    have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
    have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
    have hφb : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst b w = MvPowerSeries.substAlgHom (R := K) hsb w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsb) w).symm
        | rfl
    obtain ⟨c, hc⟩ : ∃ c, c = MvPowerSeries.constantCoeff z := ⟨_, rfl⟩
    have hcz : MvPowerSeries.constantCoeff (algebraMap K (MvPowerSeries σ K) c) = c := by
      first
        | (simp; done)
        | (simp [MvPowerSeries.algebraMap_apply]; done)
        | (simp [← MvPowerSeries.c_eq_algebraMap]; done)
        | (rw [Algebra.algebraMap_eq_smul_one]; simp; done)
        | (rw [Algebra.algebraMap_eq_smul_one, MvPowerSeries.constantCoeff_smul]; simp; done)
        | rfl
    have hw : Low 1 (z - algebraMap K (MvPowerSeries σ K) c) := by
      apply low_one
      rw [map_sub, hcz, hc, sub_self]
    obtain ⟨y, -, hy⟩ := decomp 0 (z - algebraMap K (MvPowerSeries σ K) c) hw
    have hz : z = algebraMap K (MvPowerSeries σ K) c + ∑ i, MvPowerSeries.X i * y i := by
      rw [← hy]
      abel
    have hab' : ∀ i, Agree N (a i) (b i) := fun i e he => hab i e (by omega)
    rw [hz, hφa, hφb, map_add, map_add, AlgHom.commutes, AlgHom.commutes, map_sum, map_sum,
      add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Low.sum
    intro i _
    beta_reduce
    rw [map_mul, map_mul, ← hφa, ← hφa, ← hφb, ← hφb, MvPowerSeries.subst_X hsa,
      MvPowerSeries.subst_X hsb]
    have hsplit : a i * MvPowerSeries.subst a (y i) - b i * MvPowerSeries.subst b (y i) =
        (a i - b i) * MvPowerSeries.subst a (y i) +
          b i * (MvPowerSeries.subst a (y i) - MvPowerSeries.subst b (y i)) := by ring
    rw [hsplit]
    apply Low.add
    · have h1 := Low.mul (low_of_agree (hab i))
        (show Low 0 (MvPowerSeries.subst a (y i)) from fun e he => absurd he (Nat.not_lt_zero _))
      rwa [add_zero] at h1
    · have h2 := Low.mul (low_one (hb i)) (ih (y i) a b ha hb hab')
      rwa [add_comm] at h2
private theorem low_one_subst_lemma_2 {σ τ : Type*} [Fintype σ] [Finite τ] (w : MvPowerSeries σ K)
    (hw : Low 1 w) (a : σ → MvPowerSeries τ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    Low 1 (MvPowerSeries.subst a w) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
  obtain ⟨y, -, hy⟩ := decomp 0 w hw
  rw [hy, hφa, map_sum]
  apply Low.sum
  intro i _
  beta_reduce
  rw [map_mul, ← hφa, ← hφa, MvPowerSeries.subst_X hsa]
  have h1 := Low.mul (low_one (ha i))
    (show Low 0 (MvPowerSeries.subst a (y i)) from fun e he => absurd he (Nat.not_lt_zero _))
  rwa [add_zero] at h1
end Formalism.FG.InvIntVAux
end
end

set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
namespace Formalism.FG.InvIntVAux
theorem _root_.solution {σ τ : Type*} [Fintype σ] [Finite τ] (g : MvPowerSeries σ K)
    (hg : Low 2 g) {N : ℕ} {a b : σ → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hab : ∀ i, Agree N (a i) (b i)) :
    Low (N + 1) (MvPowerSeries.subst a g - MvPowerSeries.subst b g) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
  have hφb : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst b w = MvPowerSeries.substAlgHom (R := K) hsb w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsb) w).symm
        | rfl
  obtain ⟨y, hy1, hy⟩ := decomp 1 g hg
  rw [hy, hφa, hφb, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Low.sum
  intro i _
  beta_reduce
  rw [map_mul, map_mul, ← hφa, ← hφa, ← hφb, ← hφb, MvPowerSeries.subst_X hsa,
    MvPowerSeries.subst_X hsb]
  have hsplit : a i * MvPowerSeries.subst a (y i) - b i * MvPowerSeries.subst b (y i) =
      (a i - b i) * MvPowerSeries.subst a (y i) +
        b i * (MvPowerSeries.subst a (y i) - MvPowerSeries.subst b (y i)) := by ring
  rw [hsplit]
  apply Low.add
  · exact Low.mul (low_of_agree (hab i)) (low_one_subst_lemma_2 (y i) (hy1 i) a ha)
  · have h2 := Low.mul (low_one (hb i)) (subst_diff_lemma N (y i) a b ha hb hab)
    rwa [add_comm] at h2
end Formalism.FG.InvIntVAux
