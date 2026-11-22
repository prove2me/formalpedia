-- Prove2me | solution 1 for CriticalPortraits.beta_interval_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:37:12.018193+00:00
-- url     : https://prove2.me/submissions/f865c1ae-6585-46ee-ac45-57f3ba25fa91

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Theorems.Thm_CriticalPortraits_bReach_trans
public import Theorems.Thm_CriticalPortraits_betaRoot_le
public import Theorems.Thm_CriticalPortraits_betaRoot_bReach
public import Theorems.Thm_CriticalPortraits_bReach_mem_bVerts
public import Theorems.Thm_CriticalPortraits_betaRoot_mem_block
public import Theorems.Thm_CriticalPortraits_betaRoot_min_in_block
public import Theorems.Thm_CriticalPortraits_minVal_betaBlock
public import Theorems.Thm_CriticalPortraits_betaBlock_disjoint
public import Theorems.Thm_CriticalPortraits_root_ge
public import Theorems.Thm_CriticalPortraits_descend_cross
public import Theorems.Thm_CriticalPortraits_maxVal_ge
public import Theorems.Thm_CriticalPortraits_maxVal_mem


set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {x z : ZMod (d * m)}
    (hx : x ∈ bVerts U) (hz : z ∈ bVerts U)
    (hne : betaBlock U x ≠ betaBlock U z)
    {p : ZMod (d * m)} (hp : p ∈ betaBlock U z)
    (hlo : (minVal (betaBlock U x) (betaBlock_nonempty hx)).val < p.val)
    (hhi : p.val < (maxVal (betaBlock U x) (betaBlock_nonempty hx)).val) :
    ∀ q ∈ betaBlock U z, (minVal (betaBlock U x) (betaBlock_nonempty hx)).val ≤ q.val ∧
      q.val ≤ (maxVal (betaBlock U x) (betaBlock_nonempty hx)).val := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set Xne := betaBlock_nonempty hx with hXne
  set minX := minVal (betaBlock U x) Xne with hminX
  set maxX := maxVal (betaBlock U x) Xne with hmaxX
  have hdisj : Disjoint (betaBlock U x) (betaBlock U z) := betaBlock_disjoint hne
  -- minX = betaRoot x
  have hminroot : minX = betaRoot hd hm hcanon x := minVal_betaBlock hd hm hcanon hx
  -- maxX ∈ block x; maxX.val is the block maximum
  have hmaxX_mem : maxX ∈ betaBlock U x := maxVal_mem _ Xne
  have hxreach_max : bReach U x maxX := (mem_betaBlock.mp hmaxX_mem).2
  -- p ∈ block z, so bReach z p, betaRoot z = betaRoot p
  have hzreach_p : bReach U z p := (mem_betaBlock.mp hp).2
  have hrootzp : betaRoot hd hm hcanon z = betaRoot hd hm hcanon p :=
    betaRoot_bReach hd hm hcanon hzreach_p
  -- == Step A: enclosing X-edge of p ==
  -- betaRoot maxX = betaRoot x = minX
  have hroot_max : betaRoot hd hm hcanon maxX = betaRoot hd hm hcanon x :=
    (betaRoot_bReach hd hm hcanon hxreach_max).symm
  have hroot_max_val : (betaRoot hd hm hcanon maxX).val < p.val := by
    rw [hroot_max, ← hminroot]; exact hlo
  obtain ⟨cstar, hcU, hreach_max_c, hgle, hpc⟩ :=
    descend_cross hd hm hcanon p.val maxX (le_of_lt hroot_max_val) hhi
  -- cstar ∈ block x
  have hxreach_c : bReach U x cstar := bReach_trans hxreach_max hreach_max_c
  have hc_mem : cstar ∈ betaBlock U x := by
    rw [mem_betaBlock]
    exact ⟨bReach_mem_bVerts hx hxreach_c, hxreach_c⟩
  have hclu : 1 ≤ cstar.val / m := survivor_level_pos hd hcanon hcU
  -- g* = betaParent cstar ∈ block x, g*.val ≤ p.val
  have hxreach_g : bReach U x (betaParent U cstar) :=
    bReach_trans hxreach_c (Relation.ReflTransGen.single (Or.inr ⟨hcU, hclu, rfl⟩))
  have hg_mem : betaParent U cstar ∈ betaBlock U x := by
    rw [mem_betaBlock]
    exact ⟨bReach_mem_bVerts hx hxreach_g, hxreach_g⟩
  -- minX.val ≤ g*.val (root is block-min)
  have hminX_le_g : minX.val ≤ (betaParent U cstar).val := by
    rw [hminroot]; exact betaRoot_min_in_block hd hm hcanon hg_mem
  -- g*.val < p.val (strict: else g* = p ∈ X ∩ Z)
  have hg_lt_p : (betaParent U cstar).val < p.val := by
    rcases lt_or_eq_of_le hgle with h | h
    · exact h
    · exfalso
      have : betaParent U cstar = p := ZMod.val_injective _ h
      have hpX : p ∈ betaBlock U x := by rw [← this]; exact hg_mem
      exact (Finset.disjoint_left.mp hdisj hpX) hp
  -- == Step B: lower bound. root_ge ⟹ minX.val ≤ (betaRoot p).val ==
  have hrootp_ge : (betaParent U cstar).val ≤ (betaRoot hd hm hcanon p).val :=
    root_ge hd hm hcanon hcU p (bReach_mem_bVerts hz hzreach_p) hg_lt_p hpc
  have hminX_le_rootz : minX.val ≤ (betaRoot hd hm hcanon z).val := by
    rw [hrootzp]; exact le_trans hminX_le_g hrootp_ge
  -- == the main statement ==
  intro q hq
  have hqz : bReach U z q := (mem_betaBlock.mp hq).2
  have hrootz_le_q : (betaRoot hd hm hcanon z).val ≤ q.val :=
    betaRoot_min_in_block hd hm hcanon hq
  refine ⟨le_trans hminX_le_rootz hrootz_le_q, ?_⟩
  -- upper bound by contradiction
  by_contra hqgt
  push Not at hqgt  -- maxX.val < q.val
  -- c*.val ≤ maxX.val
  have hc_le_maxX : cstar.val ≤ maxX.val := maxVal_ge _ Xne _ hc_mem
  -- (betaRoot q).val = (betaRoot z).val ≤ p.val < c*.val (root z below p, p < c*)
  have hrootq : betaRoot hd hm hcanon q = betaRoot hd hm hcanon z :=
    (betaRoot_bReach hd hm hcanon hqz).symm
  have hrootz_le_p : (betaRoot hd hm hcanon z).val ≤ p.val := by
    rw [hrootzp]; exact betaRoot_le hd hm hcanon p
  have hrootq_le_c : (betaRoot hd hm hcanon q).val ≤ cstar.val := by
    rw [hrootq]; exact le_trans hrootz_le_p (le_of_lt hpc)
  have hq_gt_c : cstar.val < q.val := lt_of_le_of_lt hc_le_maxX hqgt
  -- descend Z from q crossing c*.val
  obtain ⟨bz, hbzU, hqreach_bz, haz_le, hc_lt_bz⟩ :=
    descend_cross hd hm hcanon cstar.val q hrootq_le_c hq_gt_c
  -- bz ∈ block z, a_z = betaParent bz ∈ block z
  have hzreach_bz : bReach U z bz := bReach_trans hqz hqreach_bz
  have hbzlu : 1 ≤ bz.val / m := survivor_level_pos hd hcanon hbzU
  have hzreach_az : bReach U z (betaParent U bz) :=
    bReach_trans hzreach_bz (Relation.ReflTransGen.single (Or.inr ⟨hbzU, hbzlu, rfl⟩))
  have haz_mem : betaParent U bz ∈ betaBlock U z := by
    rw [mem_betaBlock]
    exact ⟨bReach_mem_bVerts hz hzreach_az, hzreach_az⟩
  -- a_z.val < c*.val strict (else a_z = cstar ∈ X ∩ Z)
  have haz_lt_c : (betaParent U bz).val < cstar.val := by
    rcases lt_or_eq_of_le haz_le with h | h
    · exact h
    · exfalso
      have : betaParent U bz = cstar := ZMod.val_injective _ h
      have hcZ : cstar ∈ betaBlock U z := by rw [← this]; exact haz_mem
      exact (Finset.disjoint_left.mp hdisj hc_mem) hcZ
  -- root_ge: a_z.val ≤ (betaRoot cstar).val = minX.val
  have hrootc : betaRoot hd hm hcanon cstar = betaRoot hd hm hcanon x :=
    (betaRoot_bReach hd hm hcanon hxreach_c).symm
  have haz_le_minX : (betaParent U bz).val ≤ minX.val := by
    have := root_ge hd hm hcanon hbzU cstar (bReach_mem_bVerts hx hxreach_c) haz_lt_c hc_lt_bz
    simp_all
  -- but a_z ∈ Z so a_z.val ≥ (betaRoot z).val ≥ minX.val
  have haz_ge_minX : minX.val ≤ (betaParent U bz).val :=
    le_trans hminX_le_rootz (betaRoot_min_in_block hd hm hcanon haz_mem)
  have haz_eq : (betaParent U bz).val = minX.val := le_antisymm haz_le_minX haz_ge_minX
  have haz_eq_pt : betaParent U bz = minX := ZMod.val_injective _ haz_eq
  -- minX ∈ block x; betaParent bz ∈ block z ⟹ disjoint contradiction
  have hminX_mem : minX ∈ betaBlock U x := by
    rw [hminroot]; exact betaRoot_mem_block hd hm hcanon hx
  have hminX_in_Z : minX ∈ betaBlock U z := by rw [← haz_eq_pt]; exact haz_mem
  exact (Finset.disjoint_left.mp hdisj hminX_mem) hminX_in_Z
end CriticalPortraits
