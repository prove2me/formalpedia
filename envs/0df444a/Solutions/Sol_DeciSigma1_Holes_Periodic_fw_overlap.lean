-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.fw_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:52.443127+00:00
-- url     : https://prove2.me/submissions/9f917249-1304-4e28-80dc-d405a2f8244e

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_periodicOn
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_window_isConjugate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_isPrimitive
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_period_extend_gcd
public import Theorems.Thm_DeciSigma1_Words_periodicOn_iff_hasPeriod
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {W : Fin k → List α} {dP dR : ℕ} (P : Piece W dP) (R : Piece W dR)
    (hcls : ¬ IsConjugate P.root R.root) (hd : dR ≤ dP) (hl : P.coordinate = R.coordinate) :
    min P.stop R.stop - max P.start R.start < dP + dR := by
  by_contra hge
  push Not at hge
  have hP := P.period_pos; have hR := R.period_pos
  set s := max P.start R.start
  set e := min P.stop R.stop
  have hRper : PeriodicOn (W P.coordinate) dR R.start R.stop := hl ▸ R.periodic
  have hRle : R.stop ≤ (W P.coordinate).length := hl ▸ R.stop_le_length
  have h1 : PeriodicOn (W P.coordinate) dP s e :=
      P.periodicOn.mono (le_max_left _ _) (min_le_left _ _)
  have h2 : PeriodicOn (W P.coordinate) dR s e := hRper.mono (le_max_right _ _) (min_le_right _ _)
  have hse : s ≤ e := by omega
  have he : e ≤ (W P.coordinate).length := (min_le_left _ _).trans P.stop_le_length
  have hg := period_extend_gcd hse he h1 h2 (by omega)
  have hgpos : 0 < dP.gcd dR := Nat.gcd_pos_of_pos_left _ hP
  -- the `dP`-window at `s` is a rotation of `P.root`, hence primitive
  have hwin : IsConjugate P.root (((W P.coordinate).drop s).take dP) :=
    P.window_isConjugate (le_max_left _ _) (by omega)
  have hwprim := hwin.isPrimitive P.primitive
  have hwlen : (((W P.coordinate).drop s).take dP).length = dP := by simp; omega
  have hgdP : dP.gcd dR = dP := by
    by_contra hne
    have hlt : dP.gcd dR < dP := lt_of_le_of_ne (Nat.gcd_le_left _ hP) hne
    rw [isPrimitive_iff_period] at hwprim
    apply hwprim.2 (dP.gcd dR) hgpos (by rw [hwlen]; exact hlt)
        (by rw [hwlen]; exact Nat.gcd_dvd_left _ _)
    have :=
        (periodicOn_iff_hasPeriod (w := W P.coordinate) (s := s) (e := s + dP) (by omega)
            (by omega)).mp
      (hg.mono le_rfl (by omega))
    rwa [show s + dP - s = dP by omega] at this
  have hdR : dR = dP := by
    have : dP ∣ dR := hgdP ▸ Nat.gcd_dvd_right dP dR
    exact le_antisymm hd (Nat.le_of_dvd hR this)
  subst hdR
  have hwinR : IsConjugate R.root (((W R.coordinate).drop s).take dR) :=
    R.window_isConjugate (le_max_right _ _) (by omega)
  rw [← hl] at hwinR
  exact hcls (hwin.trans hwinR.symm)
end DeciSigma1.Holes.Periodic
