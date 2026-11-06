-- Prove2me | solution 1 for FalconerPath.one_scale_middle_radial_estimates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-11-05T23:16:43.353698+00:00
-- url     : https://prove2.me/submissions/4e56b7bc-dc87-47d7-9c1f-3f29891b073a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FalconerPath_connect
import Mathlib
import Theorems.Thm_FalconerPath_quantitative_bad_directions
import Theorems.Thm_FalconerPath_middle_scale_preparation
import Theorems.Thm_FalconerPath_middle_witness_center
import Theorems.Thm_FalconerPath_middle_heavy_cell_cover
import Theorems.Thm_FalconerPath_middle_borel_deletions

noncomputable section
set_option autoImplicit false
open FalconerPath Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ConnectMiddle
/-- Absorb the two Fubini costs into half the angular deletion exponent. -/
lemma deletion_cost (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (A B c : ℝ) (hAB : A < B) (hc : 0 < c) :
    ∀ᶠ j in atTop,
      2*((scale (N j))^(-(B-A)))^c ≤ (scale (N j))^(-c*(B-A)/2) := by
  let e := c*(B-A)/2
  have he : 0 < e := by dsimp [e]; positivity
  have hR : Tendsto (fun j => scale (N j)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp hN
  have hsmall := (tendsto_rpow_neg_atTop he).comp hR
  filter_upwards [hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with j hj
  have hRpos : 0 < scale (N j) := by unfold scale; positivity
  have hpow : ((scale (N j))^(-(B-A)))^c =
      (scale (N j))^(-e) * (scale (N j))^(-e) := by
    rw [← Real.rpow_mul hRpos.le, ← Real.rpow_add hRpos]
    congr 1
    dsimp [e]
    ring
  have heq : -c*(B-A)/2 = -e := by dsimp [e]; ring
  rw [hpow, heq]
  have hp : 0 < (scale (N j))^(-e) := Real.rpow_pos_of_pos hRpos _
  have hj' : (scale (N j))^(-e) < 1/2 := hj
  calc
    2*((scale (N j))^(-e)*(scale (N j))^(-e)) =
        (2*(scale (N j))^(-e))*(scale (N j))^(-e) := by ring
    _ ≤ 1*(scale (N j))^(-e) :=
      mul_le_mul_of_nonneg_right (by linarith only [hj']) hp.le
    _ = _ := one_mul _
end ConnectMiddle

theorem solution {k : ℕ} (hk : 2 ≤ k)
    (s q ζ L a C t : ℝ) (hq : (k:ℝ)-1 ≤ q) (hqS : q < (k:ℝ)-1/2)
    (ht : (k:ℝ)-1/2 < t) (htk : t < k) (hζ : 0 < ζ)
    (hL : 0 < L) (ha : 0 < a) (hC : 0 < C)
    (X : ℕ → RadialClassData k s q ζ L a C)
    (hN : Tendsto (fun j => (X j).N) atTop atTop)
    (herr : Tendsto (fun j => (X j).err) atTop (𝓝 0))
    (m : ℝ → ℝ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ u ∈ Icc (0:ℝ) 1,
      |(X j).m u-m u| < ε)
    (A B : ℝ) (hA : 0 < A) (hAB : A < B) (hB : B < 1) (hBA : B < 2*A)
    (hmiddle : ∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A)
    (W : ℝ) (hW : 0 < W) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ j in atTop,
      ∃ H : PairSet (k+1), MeasurableSet H ∧ H ⊆ (X j).G ∧
        ((X j).ν.prod (X j).ρ) ((X j).G \ H) ≤
          ENNReal.ofReal ((scale (X j).N)^(-c₁*(B-A)/2)) ∧
        LocalFiberBounds false (X j).ρ H (fun _ => univ) (X j).v
          (contactDepths (X j).N A B) 3
          (fun i => if i = 1 then (scale (X j).N)^(-(q+c₁/2)*(B-A)) else 1) W := by
  classical
  -- Choose widths before calling the angular theorem; the final +1 pays
  -- for replacing a cell-center direction by a retained witness direction.
  obtain ⟨K, hK, cover⟩ := middle_heavy_cell_cover s q ζ L a C X hN
    A B hA hAB hB hBA W hW
  obtain ⟨c, ε, δ₀, hc, hε, hδ₀, hδ₀1, angular⟩ :=
    quantitative_bad_directions hk q t ζ ((k:ℝ)+2) (K+1)
      hq hqS.le ht htk hζ (by positivity) (by linarith)
  have prep := middle_scale_preparation s q ζ L a C t X hN herr m hconv
    A B hA hAB hB hmiddle ε δ₀ hε hδ₀
  have robust := middle_witness_center s q ζ L a C X hN
    A B hA hAB hB hBA K c hK hc
  refine ⟨c, hc, ?_⟩
  filter_upwards [prep, robust, cover c hc,
    ConnectMiddle.deletion_cost (fun j => (X j).N) hN A B c hAB hc] with j hp hr hcover hcost
  dsimp only at hp hr hcover
  let D := (scale (X j).N)^(-(B-A))
  let d := contactDepths (X j).N A B 1
  let b := contactDepths (X j).N A B 2
  obtain ⟨hD, hD1, hDδ, hsource, hlaws⟩ := hp
  -- A single envelope per cell works for all reverse laws, including those
  -- at different witnesses. No direction law is renormalized here.
  have envelopes : ∀ i : Fin (k+1) → ℤ,
      ∃ Bplus : Set (Space (k+1)), MeasurableSet Bplus ∧
        (0 < (X j).ρ (dyadicCell (X j).v d i) →
          badDirections (connectCellLaw (X j).ρ (X j).v d i)
            ((k:ℝ)+2) (K+1) D q c ⊆ Bplus) ∧
        (∀ᵐ z ∂(X j).ρ,
          reverseDirection (X j).ν (X j).G z Bplus ≤ ENNReal.ofReal (D^c)) := by
    intro i
    by_cases hQ : 0 < (X j).ρ (dyadicCell (X j).v d i)
    · obtain ⟨hprob, hcar, hball⟩ := hsource i hQ
      obtain ⟨Bplus, hB, hBsphere, hbad, hall⟩ :=
        angular D hD hDδ (connectCellLaw (X j).ρ (X j).v d i) hprob hcar hball
      refine ⟨Bplus, hB, fun _ => hbad, ?_⟩
      filter_upwards [hlaws] with z hz
      exact hall _ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    · refine ⟨∅, MeasurableSet.empty, fun h => (hQ h).elim, ?_⟩
      exact Eventually.of_forall (fun _ => by simp)
  choose Bplus hB hbad hreverse using envelopes
  have heavy : ∀ i : Fin (k+1) → ℤ,
      0 < (X j).ρ (dyadicCell (X j).v d i) → ∀ x ∈ (X j).ν.support,
      (∃ z ∈ dyadicCell (X j).v d i,
        z ∈ (X j).ρ.support ∧ (x,z) ∈ (X j).G ∧ radial z x ∉ Bplus i) →
      normalizedRestriction (X j).ρ (dyadicCell (X j).v d i)
        (connectHeavy (X j).ρ (dyadicCell (X j).v d i)
          (W*mesh b) (D^(q+c/2)) x) ≤ ENNReal.ofReal (D^c) := by
    intro i hQ x hx hwitness
    obtain ⟨z, hzQ, hzsupp, hzG, hzgood⟩ := hwitness
    obtain ⟨anchors, hcount, hdom⟩ := hcover i hQ x hx
    by_contra hmass
    have hlarge := (lt_of_not_ge hmass).le.trans hdom
    exact hzgood ((hbad i hQ) (hr i hQ x hx z hzQ hzsupp anchors hcount hlarge))
  obtain ⟨H, hH, hHG, hdelete, hlocal⟩ := middle_borel_deletions
    (X j).ν (X j).ρ (X j).probν (X j).probρ (X j).G (X j).measurable (X j).supported
    (X j).v d (W*mesh b) (D^(q+c/2)) (D^c) (by positivity) (by positivity)
    Bplus hB (fun i => (hreverse i).mono (fun _ hz _ => hz)) heavy
  refine ⟨H, hH, hHG, hdelete.trans (ENNReal.ofReal_le_ofReal hcost), ?_⟩
  have hRpos : 0 < scale (X j).N := by unfold scale; positivity
  have hfactor : D^(q+c/2) = (scale (X j).N)^(-(q+c/2)*(B-A)) := by
    dsimp [D]
    rw [← Real.rpow_mul hRpos.le]
    congr 1
    ring
  intro i hi x z hx cell hz
  by_cases hi1 : i = 1
  · subst i
    simpa [connectRadialMass, hfactor, d, b] using hlocal x z hx cell hz
  · simp only [if_neg hi1, ENNReal.ofReal_one, one_mul]
    exact measure_mono (fun z' hz' => hz'.1)
