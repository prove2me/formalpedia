-- Prove2me | solution 1 for BSUMConv.SUM.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T16:35:43.596636+00:00
-- url     : https://prove2.me/submissions/f3e956ed-9599-41a3-aa42-8f8b5e9a1f71

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_SUM_Setting

set_option autoImplicit false

namespace BSUMProbe9381

open Filter Topology TsengBCD.Stationary BSUMConv.SUM

/-- The sequence of objective values along a SUM run is antitone. -/
theorem f_antitone {m : ℕ} (Xset : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (u : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hA : Assumption1 Xset f u)
    (x : ℕ → EuclideanSpace ℝ (Fin m)) (hx : IsSUMRun Xset u x) :
    Antitone (fun r => f (x r)) := by
  have hmem : ∀ r, x r ∈ Xset := by
    intro r; cases r with
    | zero => exact hx.1
    | succ r => exact (hx.2 r).1
  apply antitone_nat_of_succ_le
  intro r
  have h1 := hA.2.1 (x (r + 1)) (hmem (r + 1)) (x r) (hmem r)
  have h2 := (hx.2 r).2 (x r) (hmem r)
  have h3 := hA.1 (x r) (hmem r)
  show f (x (r + 1)) ≤ f (x r)
  linarith

/-- The key inequality: `u z z ≤ u y z` for every feasible `y`. -/
theorem key_ineq {m : ℕ} (Xset : Set (EuclideanSpace ℝ (Fin m)))
    (hclosed : IsClosed Xset)
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (u : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hA : Assumption1 Xset f u)
    (x : ℕ → EuclideanSpace ℝ (Fin m)) (hx : IsSUMRun Xset u x)
    (z : EuclideanSpace ℝ (Fin m)) (hz : MapClusterPt z atTop x) :
    z ∈ Xset ∧ ∀ y ∈ Xset, u z z ≤ u y z := by
  have hmem : ∀ r, x r ∈ Xset := by
    intro r; cases r with
    | zero => exact hx.1
    | succ r => exact (hx.2 r).1
  have hzX : z ∈ Xset :=
    hclosed.mem_of_mapClusterPt hz (Eventually.of_forall hmem)
  have hanti := f_antitone Xset f u hA x hx
  have hcont := hA.2.2.2
  -- diagonal continuity
  have hdiag : ContinuousOn (fun y => u y y) Xset := by
    have : ContinuousOn (fun y : EuclideanSpace ℝ (Fin m) => (y, y)) Xset :=
      (continuous_id.prodMk continuous_id).continuousOn
    exact hcont.comp this (fun y hy => ⟨hy, hy⟩)
  -- lower bound on all values
  have hlow : ∀ r, u z z ≤ f (x r) := by
    intro N
    by_contra hlt
    rw [not_le] at hlt
    have hS : IsClosed (Xset ∩ (fun y => u y y) ⁻¹' Set.Iic (f (x N))) :=
      hdiag.preimage_isClosed_of_isClosed hclosed isClosed_Iic
    have hev : ∀ᶠ r in atTop, x r ∈ Xset ∩ (fun y => u y y) ⁻¹' Set.Iic (f (x N)) := by
      filter_upwards [eventually_ge_atTop N] with r hr
      refine ⟨hmem r, ?_⟩
      show u (x r) (x r) ≤ f (x N)
      rw [hA.1 (x r) (hmem r)]
      exact hanti hr
    have hzS := hS.mem_of_mapClusterPt hz hev
    have : u z z ≤ f (x N) := hzS.2
    linarith
  refine ⟨hzX, fun y hy => ?_⟩
  have hcy : ContinuousOn (fun w => u y w) Xset := by
    have : ContinuousOn (fun w : EuclideanSpace ℝ (Fin m) => (y, w)) Xset :=
      (continuous_const.prodMk continuous_id).continuousOn
    exact hcont.comp this (fun w hw => ⟨hy, hw⟩)
  have hS : IsClosed (Xset ∩ (fun w => u y w) ⁻¹' Set.Ici (u z z)) :=
    hcy.preimage_isClosed_of_isClosed hclosed isClosed_Ici
  have hev : ∀ᶠ r in atTop, x r ∈ Xset ∩ (fun w => u y w) ⁻¹' Set.Ici (u z z) := by
    refine Eventually.of_forall (fun r => ⟨hmem r, ?_⟩)
    show u z z ≤ u y (x r)
    have h1 := hA.2.1 (x (r + 1)) (hmem (r + 1)) (x r) (hmem r)
    have h2 := (hx.2 r).2 y hy
    have h3 := hlow (r + 1)
    linarith
  exact (hS.mem_of_mapClusterPt hz hev).2

end BSUMProbe9381

open Filter Topology in
theorem solution {m : ℕ} (Xset : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ Xset) (hclosed : IsClosed Xset)
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (u : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hA : BSUMConv.SUM.Assumption1 Xset f u)
    (x : ℕ → EuclideanSpace ℝ (Fin m)) (hx : BSUMConv.SUM.IsSUMRun Xset u x)
    (z : EuclideanSpace ℝ (Fin m)) (hz : MapClusterPt z atTop x) :
    BSUMConv.SUM.IsStationaryOn Xset f z := by
  obtain ⟨hzX, hkey⟩ := BSUMProbe9381.key_ineq Xset hclosed f u hA x hx z hz
  refine ⟨hzX, fun d hd => ?_⟩
  rw [← hA.2.2.1 z hzX d hd]
  unfold TsengBCD.Stationary.dirDeriv
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hmemt : z + t • d ∈ Xset := hconv.add_smul_mem hzX hd ⟨ht.1.le, ht.2.le⟩
  have hle := hkey (z + t • d) hmemt
  rw [← EReal.coe_sub, ← EReal.coe_mul]
  exact EReal.coe_nonneg.mpr (mul_nonneg (by linarith) (inv_nonneg.mpr ht.1.le))
