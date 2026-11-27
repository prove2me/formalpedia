-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.lap_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:17:26.508799+00:00
-- url     : https://prove2.me/submissions/96642e37-40e3-467e-9994-e7e5112a25f2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_pderiv_subG_lam
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_pderiv_subG_off
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_RF_pderiv_comm__6c5c66fe37bd
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_a1
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
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) (o : Orb) (t : ZMod 2)
    (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hno : ∀ ρ g1 g2, g1 ≠ g2 → (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ Q.vars →
      (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars → False) :
    ∑ b, pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
      (subG r tau gm plc Q)) = 0 := by
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map plc →
      pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
        (subG r tau gm plc Q)) = 0 := by
    intro b _ hb
    rw [pderiv_subG_off plc (ℓ := ⟨tau o (t + 1), a2, b⟩), map_zero]
    intro z e
    apply hb
    rw [Finset.mem_map]
    exact ⟨(z.1.1, z.2), Finset.mem_univ _, (congrArg (fun ℓ : Letter T r n => ℓ.2.2) e).symm⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map plc)) hoff, Finset.sum_map, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hf : ∀ col, pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n)
      (pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q)) =
      ∑ g1, ∑ g2, MvPolynomial.C (gm o t col g1 * gm o (t + 1) col g2) *
        subG r tau gm plc (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
          (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) := by
    intro col
    have e2 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t + 1, a2⟩⟩) : AA r tau N) col Q
    have e2' : pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q) = _ := e2
    rw [e2', map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g2 _ => ?_
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
    have e1 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t, a1⟩⟩) : AA r tau N) col
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)
    have e1' : pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) = _ := e1
    rw [e1', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g1 _ => ?_
    rw [map_mul]
    unfold Gm
    ring
  simp only [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g2 _ => ?_
  rw [← Finset.sum_mul, ← map_sum]
  by_cases hg : g1 = g2
  · have hK : ∑ col, gm o t col g1 * gm o (t + 1) col g2 = 0 := by
      have h := gm_hyp o t g2 g1
      rw [if_pos hg.symm] at h
      rw [← h]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    rw [hK, map_zero, zero_mul]
  · have hz : pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
        (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q) = 0 := by
      by_cases h2 : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars
      · have h1 : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∉ Q.vars := fun h1 => hno ρ g1 g2 hg h1 h2
        rw [pderiv_comm', pderiv_eq_zero_of_notMem_vars h1, map_zero]
      · rw [pderiv_eq_zero_of_notMem_vars h2, map_zero]
    rw [hz, map_zero, mul_zero]
end Formalism.L2.FormalSeriesBounds.RF
