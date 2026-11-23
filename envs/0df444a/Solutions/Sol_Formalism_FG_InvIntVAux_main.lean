-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:03.297803+00:00
-- url     : https://prove2.me/submissions/279187a6-664e-47bd-b164-f1af5e7a1997

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Theorems.Thm_Formalism_FG_InvIntVAux_low_subst_diff
import Theorems.Thm_Formalism_FG_InvIntVAux_tail_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
namespace Formalism.FG.InvIntVAux
theorem _root_.solution (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (P i) = 0) →
      (∀ i, IntegralMv (P i)) → C (fun j => MvPowerSeries.subst P (f j)))
    (hlowC : ∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1)
    (h : ι → MvPowerSeries τ K) (hh0 : ∀ i, MvPowerSeries.constantCoeff (h i) = 0)
    (hCh : C (fun j => MvPowerSeries.subst h (f j))) : ∀ i, IntegralMv (h i) := by
  classical
  have hcc : ∀ x : MvPowerSeries τ K, MvPowerSeries.constantCoeff x = MvPowerSeries.coeff 0 x :=
    fun x => by first | rfl | simp
  have hdz : ∀ e : τ →₀ ℕ, e.degree = 0 → e = 0 := fun e he => by
    first
      | exact (Finsupp.degree_eq_zero_iff e).1 he
      | exact Finsupp.degree_eq_zero_iff.1 he
      | simpa using he
  have hd0 : (0 : τ →₀ ℕ).degree = 0 := by
    first | rfl | simp
  have hsubX : ∀ (a : ι → MvPowerSeries τ K), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) →
      ∀ j, MvPowerSeries.subst a (f j) =
        a j + MvPowerSeries.subst a (f j - MvPowerSeries.X j) := by
    intro a ha j
    have hs : MvPowerSeries.HasSubst a := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
            (fun s => by rw [ha s]; exact IsNilpotent.zero)
        | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩
    have hsub' : MvPowerSeries.subst a (f j - MvPowerSeries.X j) =
        MvPowerSeries.subst a (f j) -
          MvPowerSeries.subst a (MvPowerSeries.X j : MvPowerSeries ι K) := by
      first
        | exact MvPowerSeries.subst_sub hs _ _
        | rw [eq_sub_iff_add_eq, ← MvPowerSeries.subst_add hs, sub_add_cancel]
        | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_sub _ _ _)
    rw [hsub', MvPowerSeries.subst_X hs]
    abel
  have key : ∀ N : ℕ, ∀ i (d : τ →₀ ℕ), d.degree < N →
      ‖MvPowerSeries.coeff d (h i)‖ ≤ 1 := by
    intro N
    induction N with
    | zero => intro i d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ N ih =>
      intro i d hd
      rcases Nat.lt_or_ge d.degree N with hlt | hge
      · exact ih i d hlt
      have hdN : d.degree = N := by omega
      rcases Nat.eq_zero_or_pos N with hN | hN
      · have hd00 : d = 0 := hdz d (by omega)
        subst hd00
        rw [← hcc, hh0 i, norm_zero]
        exact zero_le_one
      obtain ⟨P, hPc⟩ : ∃ P : ι → MvPowerSeries τ K, ∀ j e,
          MvPowerSeries.coeff e (P j) =
            if e.degree < N then MvPowerSeries.coeff e (h j) else 0 :=
        ⟨fun j e => if e.degree < N then MvPowerSeries.coeff e (h j) else 0, fun j e => rfl⟩
      have h0N : (0 : τ →₀ ℕ).degree < N := by rw [hd0]; exact hN
      have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := by
        intro j
        rw [hcc, hPc, if_pos h0N, ← hcc, hh0 j]
      have hPint : ∀ j, IntegralMv (P j) := by
        intro j e
        rw [hPc]
        split_ifs with he
        · exact ih j e he
        · rw [norm_zero]
          exact zero_le_one
      have hagree : ∀ j, Agree N (h j) (P j) := by
        intro j e he
        rw [hPc, if_pos he]
      have hCP := hP P hP0 hPint
      have hCD := hsub _ _ hCh hCP
      have hDc : ∀ j (e : τ →₀ ℕ), e.degree ≤ N →
          MvPowerSeries.coeff e (((fun j : ι => MvPowerSeries.subst h (f j)) -
            (fun j : ι => MvPowerSeries.subst P (f j))) j) =
          if e.degree < N then 0 else MvPowerSeries.coeff e (h j) := by
        intro j e he
        have hL := low_subst_diff (f j - MvPowerSeries.X j) (tail_low f hf j) hh0 hP0 hagree
        simp only [Pi.sub_apply]
        rw [hsubX h hh0 j, hsubX P hP0 j]
        have hrw : h j + MvPowerSeries.subst h (f j - MvPowerSeries.X j) -
            (P j + MvPowerSeries.subst P (f j - MvPowerSeries.X j)) =
            (h j - P j) + (MvPowerSeries.subst h (f j - MvPowerSeries.X j) -
              MvPowerSeries.subst P (f j - MvPowerSeries.X j)) := by abel
        have he1 : e.degree < N + 1 := by omega
        rw [hrw, map_add, hL e he1, add_zero, map_sub, hPc]
        split_ifs with h1
        · exact sub_self _
        · exact sub_zero _
      have hvan : ∀ j (e : τ →₀ ℕ), e.degree < N →
          MvPowerSeries.coeff e (((fun j : ι => MvPowerSeries.subst h (f j)) -
            (fun j : ι => MvPowerSeries.subst P (f j))) j) = 0 := by
        intro j e he
        rw [hDc j e he.le, if_pos he]
      have hN1 : 1 ≤ N := by omega
      have hb := hlowC _ hCD N hN1 hvan i d hdN
      have hnlt : ¬ d.degree < N := by omega
      rw [hDc i d hdN.le, if_neg hnlt] at hb
      exact hb
  intro i d
  exact key (d.degree + 1) i d (Nat.lt_succ_self _)
end Formalism.FG.InvIntVAux
