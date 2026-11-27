-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.Supplement.infinite_horizon_base_stock
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:04.536739+00:00
-- url     : https://prove2.me/submissions/afc960e8-cfe4-4c60-9414-7f4683ea9e0b

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ControlSystem
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_Stationary
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

open MeasureTheory Filter Topology

open GallegoOzerADI
open GallegoOzerADI.PositiveSetup
open GallegoOzerADI.PositiveSetup.Supplement

/-- Theorem 6 (p. 1352), stationary zero set-up cost (`K = 0`), infinite horizon, with the
global uniform convergence of Parts 1–2 corrected to uniform convergence on every half-line
`(-∞, B]` (see the item's Differences from the source). `myopicOrderUpTo G` is
`y^m = min {y : G(y) = min_x G(x)}`. -/
theorem solution {L M : ℕ} [NeZero M] (G : ℝ → ℝ) (α : ℝ)
    (μ : Measure (Fin (L + M + 2) → ℝ)) [IsProbabilityMeasure μ]
    (hG_convex : ConvexOn ℝ Set.univ G) (hG_coercive : Tendsto G (cocompact ℝ) atTop)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hμ_nonneg : ∀ᵐ D ∂μ, ∀ k, 0 ≤ D k) :
    ∃ J V : ℝ → (Fin M → ℝ) → ℝ, ∀ o : Fin M → ℝ, 0 ≤ o →
      -- Part 1
      ((∀ B : ℝ, TendstoUniformlyOn (fun n x => Jgo G 0 α μ n x o) (fun x => J x o) atTop
          (Set.Iic B)) ∧
        ConvexOn ℝ Set.univ (fun x => J x o) ∧ Tendsto (fun x => J x o) atTop atTop) ∧
      -- Part 2
      ((∀ B : ℝ, TendstoUniformlyOn (fun n y => Vgo G 0 α μ n y o) (fun y => V y o) atTop
          (Set.Iic B)) ∧
        ConvexOn ℝ Set.univ (fun y => V y o) ∧ Tendsto (fun y => V y o) (cocompact ℝ) atTop ∧
        ∃ y, ∀ z, V y o ≤ V z o) ∧
      -- Part 3
      (IsLeast {y | ∀ z, V y o ≤ V z o} (myopicOrderUpTo G) ∧
        ∀ x : ℝ, (adiSystem (L := L) G 0).IsOptimalFrom α μ
          (baseStockPolicy (myopicOrderUpTo G)) (x, o)) := by
            classical
            -- facts on G and m
            have hGc : Continuous G := by
              have h := hG_convex.continuousOn_interior
              rw [interior_univ] at h
              exact continuousOn_univ.mp h
            obtain ⟨m, hm⟩ : ∃ m, m = myopicOrderUpTo G := ⟨_, rfl⟩
            have hmset : IsLeast {y : ℝ | ∀ x, G y ≤ G x} m := by
              rw [hm]
              have hne : {y : ℝ | ∀ x, G y ≤ G x}.Nonempty :=
                hGc.exists_forall_le hG_coercive
              have hcl : IsClosed {y : ℝ | ∀ x, G y ≤ G x} := by
                rw [Set.ofPred_forall]
                exact isClosed_iInter fun x => isClosed_le hGc continuous_const
              have hbd : BddBelow {y : ℝ | ∀ x, G y ≤ G x} := by
                have h1 : Tendsto G atBot atTop := hG_coercive.mono_left atBot_le_cocompact
                obtain ⟨y0, hy0⟩ := hne
                obtain ⟨b, hb⟩ := (h1.eventually (eventually_gt_atTop (G y0))).exists_forall_of_atBot
                refine ⟨b, fun y hy => ?_⟩
                by_contra hlt
                have := hb y (by linarith [not_le.mp hlt])
                have h2 := hy y0
                linarith
              exact ⟨hcl.csInf_mem hne hbd, fun y hy => csInf_le hbd hy⟩
            have hmin : ∀ x, G m ≤ G x := hmset.1
            have hlt : ∀ y, y < m → G m < G y := by
              intro y hy
              by_contra h
              have : y ∈ {y : ℝ | ∀ x, G y ≤ G x} := fun x => le_trans (not_lt.mp h) (hmin x)
              exact absurd (hmset.2 this) (not_le.mpr hy)
            have hmono : ∀ a b, m ≤ a → a ≤ b → G a ≤ G b := by
              intro a b ha hab
              have h1 := hG_convex.le_max_of_mem_Icc (Set.mem_univ m) (Set.mem_univ b)
                (show a ∈ Set.Icc m b from ⟨ha, hab⟩)
              rwa [max_eq_right (hmin b)] at h1
            obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun x => G (max x m) - G m + |G m| := ⟨_, rfl⟩
            have hψ0 : ∀ x, 0 ≤ ψ x := by
              intro x; rw [hψ]; have := hmin (max x m); have := abs_nonneg (G m); simp only; linarith
            have hψm : Monotone ψ := by
              intro a b hab
              rw [hψ]
              have := hmono (max a m) (max b m) (le_max_right _ _) (max_le_max hab le_rfl)
              simp only; linarith
            have hψmax : ∀ x, ψ (max x m) = ψ x := by
              intro x; rw [hψ]; simp
            have hGψ : ∀ x, |G (max x m)| ≤ ψ x := by
              intro x
              rw [hψ]
              have h1 := hmin (max x m)
              have h2 : G (max x m) = (G (max x m) - G m) + G m := by ring
              calc |G (max x m)| = |(G (max x m) - G m) + G m| := by rw [← h2]
                _ ≤ |G (max x m) - G m| + |G m| := abs_add_le _ _
                _ = _ := by rw [abs_of_nonneg (by linarith)]
            have hα' : 0 < 1 - α := by linarith
            -- transitions
            have hobs : ∀ (o : Fin M → ℝ), 0 ≤ o → ∀ j, 0 ≤ obsComp o j := by
              intro o ho j
              unfold obsComp
              split_ifs with h
              · exact ho _
              · exact le_rfl
            have hnx : ∀ (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ), 0 ≤ o → (∀ k, 0 ≤ D k) →
                nextX y o D ≤ y := by
              intro y o D ho hD
              unfold nextX
              have h1 := hobs o ho 0
              have h2 : 0 ≤ ∑ k : Fin (L + 2), D (Fin.castLE (by omega) k) :=
                Finset.sum_nonneg fun k _ => hD _
              linarith
            have hno : ∀ (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ), 0 ≤ o → (∀ k, 0 ≤ D k) →
                0 ≤ nextO o D := by
              intro o D ho hD j
              exact add_nonneg (hobs o ho _) (hD _)
            have hobsM : ∀ j, Measurable (fun o : Fin M → ℝ => obsComp o j) := by
              intro j
              unfold obsComp
              split_ifs with h
              · exact measurable_pi_apply _
              · exact measurable_const
            have hnxM : Measurable (fun p : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
                nextX p.1.1 p.1.2 p.2) := by
              unfold nextX
              refine (measurable_fst.fst.sub ?_).sub ((hobsM 0).comp measurable_fst.snd)
              exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).comp measurable_snd
            have hnoM : Measurable (fun p : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
                nextO p.1.2 p.2) := by
              unfold nextO
              refine measurable_pi_lambda _ fun j => ?_
              exact ((hobsM _).comp measurable_fst.snd).add ((measurable_pi_apply _).comp measurable_snd)
            -- the good-function predicate
            obtain ⟨Good, hGood⟩ : ∃ Good : (ℝ → (Fin M → ℝ) → ℝ) → Prop, Good = fun f =>
                (∃ F : ℝ × (Fin M → ℝ) → ℝ, Measurable F ∧ ∀ x o, 0 ≤ o → f x o = F (x, o)) ∧
                (∀ o, 0 ≤ o → Monotone (fun x => f x o)) ∧
                (∀ o, 0 ≤ o → ConvexOn ℝ Set.univ (fun x => f x o)) ∧
                (∀ o, 0 ≤ o → ∀ x, x ≤ m → f x o = f m o) ∧
                (∀ o, 0 ≤ o → ∀ x, |f x o| ≤ ψ x / (1 - α)) := ⟨_, rfl⟩
            -- integrability
            have hInt : ∀ f, Good f → ∀ o, 0 ≤ o → ∀ y,
                Integrable (fun D => f (nextX y o D) (nextO o D)) μ := by
              intro f hf o ho y
              rw [hGood] at hf
              obtain ⟨⟨F, hFm, hF⟩, -, -, -, hb⟩ := hf
              refine Integrable.of_bound (C := ψ y / (1 - α)) ?_ ?_
              · refine AEStronglyMeasurable.congr (f := fun D => F (nextX y o D, nextO o D)) ?_ ?_
                · apply Measurable.aestronglyMeasurable
                  refine hFm.comp (Measurable.prodMk ?_ ?_)
                  · exact hnxM.comp (measurable_const.prodMk measurable_id : Measurable
                      (fun D : Fin (L + M + 2) → ℝ => ((y, o), D)))
                  · exact hnoM.comp (measurable_const.prodMk measurable_id : Measurable
                      (fun D : Fin (L + M + 2) → ℝ => ((y, o), D)))
                · filter_upwards [hμ_nonneg] with D hD
                  exact (hF _ _ (hno o D ho hD)).symm
              · filter_upwards [hμ_nonneg] with D hD
                rw [Real.norm_eq_abs]
                refine (hb _ (hno o D ho hD) _).trans ?_
                exact div_le_div_of_nonneg_right (hψm (hnx y o D ho hD)) hα'.le
            -- properties of the integral
            have hI : ∀ f, Good f → ∀ o, 0 ≤ o →
                Monotone (fun y => ∫ D, f (nextX y o D) (nextO o D) ∂μ) ∧
                ConvexOn ℝ Set.univ (fun y => ∫ D, f (nextX y o D) (nextO o D) ∂μ) ∧
                (∀ y, y ≤ m → ∫ D, f (nextX y o D) (nextO o D) ∂μ = ∫ D, f (nextX m o D) (nextO o D) ∂μ) ∧
                (∀ y, |∫ D, f (nextX y o D) (nextO o D) ∂μ| ≤ ψ y / (1 - α)) := by
              intro f hf o ho
              have hint := hInt f hf o ho
              rw [hGood] at hf
              obtain ⟨-, hfm, hfc, hfk, hb⟩ := hf
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro a b hab
                refine integral_mono_ae (hint a) (hint b) ?_
                filter_upwards [hμ_nonneg] with D hD
                refine hfm _ (hno o D ho hD) ?_
                unfold nextX; linarith
              · refine ⟨convex_univ, ?_⟩
                intro x _ y _ a b ha hb' hab
                simp only [smul_eq_mul]
                rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hint x).const_mul a)
                  ((hint y).const_mul b)]
                refine integral_mono_ae (hint _) (((hint x).const_mul a).add ((hint y).const_mul b)) ?_
                filter_upwards [hμ_nonneg] with D hD
                have h1 := (hfc _ (hno o D ho hD)).2 (Set.mem_univ (nextX x o D))
                  (Set.mem_univ (nextX y o D)) ha hb' hab
                simp only [smul_eq_mul] at h1
                have h2 : nextX (a * x + b * y) o D = a * nextX x o D + b * nextX y o D := by
                  unfold nextX
                  have : b = 1 - a := by linarith
                  subst this
                  ring
                rw [h2]
                exact h1
              · intro y hy
                refine integral_congr_ae ?_
                filter_upwards [hμ_nonneg] with D hD
                have h0 := hno o D ho hD
                rw [hfk _ h0 _ ((hnx y o D ho hD).trans hy), hfk _ h0 _ (hnx m o D ho hD)]
              · intro y
                have h1 : ‖∫ D, f (nextX y o D) (nextO o D) ∂μ‖ ≤ (ψ y / (1 - α)) * μ.real Set.univ := by
                  refine norm_integral_le_of_norm_le_const ?_
                  filter_upwards [hμ_nonneg] with D hD
                  rw [Real.norm_eq_abs]
                  refine (hb _ (hno o D ho hD) _).trans ?_
                  exact div_le_div_of_nonneg_right (hψm (hnx y o D ho hD)) hα'.le
                simpa using h1
            -- V min
            have hVprop : ∀ f, Good f → ∀ o, 0 ≤ o →
                (∀ z, G m + α * ∫ D, f (nextX m o D) (nextO o D) ∂μ ≤
                  G z + α * ∫ D, f (nextX z o D) (nextO o D) ∂μ) ∧
                (∀ a b, m ≤ a → a ≤ b → G a + α * ∫ D, f (nextX a o D) (nextO o D) ∂μ ≤
                  G b + α * ∫ D, f (nextX b o D) (nextO o D) ∂μ) ∧
                ConvexOn ℝ Set.univ (fun y => G y + α * ∫ D, f (nextX y o D) (nextO o D) ∂μ) := by
              intro f hf o ho
              obtain ⟨h1, h2, h3, h4⟩ := hI f hf o ho
              have hmon : ∀ a b, m ≤ a → a ≤ b → G a + α * ∫ D, f (nextX a o D) (nextO o D) ∂μ ≤
                  G b + α * ∫ D, f (nextX b o D) (nextO o D) ∂μ := by
                intro a b ha hab
                exact add_le_add (hmono a b ha hab) (mul_le_mul_of_nonneg_left (h1 hab) hα₀.le)
              refine ⟨?_, hmon, ?_⟩
              · intro z
                rcases le_total m z with hz | hz
                · exact hmon m z le_rfl hz
                · rw [h3 z hz]
                  linarith [hmin z]
              · exact hG_convex.add (h2.smul hα₀.le)
            have hStep : ∀ f, Good f → ∀ o, 0 ≤ o → ∀ x,
                orderCost 0 (fun y => G y + α * ∫ D, f (nextX y o D) (nextO o D) ∂μ) x =
                  G (max x m) + α * ∫ D, f (nextX (max x m) o D) (nextO o D) ∂μ := by
              intro f hf o ho x
              obtain ⟨h1, h2, -⟩ := hVprop f hf o ho
              have key : ∀ y : {y : ℝ // x ≤ y},
                  G (max x m) + α * ∫ D, f (nextX (max x m) o D) (nextO o D) ∂μ ≤
                  0 * setupIndicator ((y : ℝ) - x) +
                    (G y + α * ∫ D, f (nextX y o D) (nextO o D) ∂μ) := by
                rintro ⟨y, hy⟩
                simp only [zero_mul, zero_add]
                rcases le_total x m with hx | hx
                · rw [max_eq_right hx]; exact h1 y
                · rw [max_eq_left hx]; exact h2 x y hx hy
              unfold orderCost
              have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
              apply le_antisymm
              · refine (ciInf_le (f := fun y : {y : ℝ // x ≤ y} => 0 * setupIndicator ((y : ℝ) - x) +
                    (G y + α * ∫ D, f (nextX y o D) (nextO o D) ∂μ))
                    ⟨G (max x m) + α * ∫ D, f (nextX (max x m) o D) (nextO o D) ∂μ, ?_⟩
                    (⟨max x m, le_max_left _ _⟩ : {y : ℝ // x ≤ y})).trans ?_
                · rintro _ ⟨y, rfl⟩
                  exact key y
                · simp
              · exact le_ciInf key
            -- all Jgo are good
            have hJgood : ∀ n, Good (Jgo G 0 α μ n) := by
              intro n
              induction n with
              | zero =>
                rw [hGood]
                refine ⟨⟨fun _ => 0, measurable_const, fun _ _ _ => rfl⟩, fun o _ => monotone_const,
                  fun o _ => convexOn_const 0 convex_univ, fun _ _ _ _ => rfl, fun o _ x => ?_⟩
                simp only [Jgo, abs_zero]
                exact div_nonneg (hψ0 x) hα'.le
              | succ n ih =>
                have hst : ∀ o, 0 ≤ o → ∀ x, Jgo G 0 α μ (n + 1) x o =
                    G (max x m) + α * ∫ D, Jgo G 0 α μ n (nextX (max x m) o D) (nextO o D) ∂μ :=
                  fun o ho x => hStep _ ih o ho x
                have ih' := ih
                rw [hGood] at ih
                obtain ⟨⟨F, hFm, hF⟩, -⟩ := ih
                rw [hGood]
                refine ⟨⟨fun p => G (max p.1 m) + α * ∫ D, F (nextX (max p.1 m) p.2 D, nextO p.2 D) ∂μ,
                  ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
                · refine (hGc.measurable.comp (measurable_fst.max measurable_const)).add
                    (Measurable.const_mul ?_ α)
                  have hsm : StronglyMeasurable (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
                      F (nextX (max q.1.1 m) q.1.2 q.2, nextO q.1.2 q.2)) := by
                    apply Measurable.stronglyMeasurable
                    refine hFm.comp (Measurable.prodMk ?_ hnoM)
                    exact hnxM.comp (((measurable_fst.fst.max measurable_const).prodMk
                      measurable_fst.snd).prodMk measurable_snd)
                  exact (hsm.integral_prod_right').measurable
                · intro x o ho
                  rw [hst o ho x]
                  congr 2
                  refine integral_congr_ae ?_
                  filter_upwards [hμ_nonneg] with D hD
                  exact hF _ _ (hno o D ho hD)
                · intro o ho a b hab
                  simp only [hst o ho]
                  exact (hVprop _ ih' o ho).2.1 _ _ (le_max_right _ _) (max_le_max hab le_rfl)
                · intro o ho
                  refine ⟨convex_univ, ?_⟩
                  intro x _ y _ a b ha hb hab
                  simp only [hst o ho]
                  obtain ⟨-, h2, h3⟩ := hVprop _ ih' o ho
                  have h4 := h3.2 (Set.mem_univ (max x m)) (Set.mem_univ (max y m)) ha hb hab
                  refine le_trans (h2 _ _ (le_max_right _ _) ?_) h4
                  simp only [smul_eq_mul]
                  apply max_le
                  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
                      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
                  · have e1 : m = a * m + b * m := by rw [← add_mul, hab, one_mul]
                    have e2 := mul_le_mul_of_nonneg_left (le_max_right x m) ha
                    have e3 := mul_le_mul_of_nonneg_left (le_max_right y m) hb
                    linarith
                · intro o ho x hx
                  simp only [hst o ho, max_eq_right hx, max_self]
                · intro o ho x
                  rw [hst o ho]
                  have h4 := (hI _ ih' o ho).2.2.2 (max x m)
                  rw [hψmax] at h4
                  calc _ ≤ |G (max x m)| + |α * ∫ D, Jgo G 0 α μ n (nextX (max x m) o D) (nextO o D) ∂μ| :=
                        abs_add_le _ _
                    _ ≤ ψ x + α * (ψ x / (1 - α)) := by
                        rw [abs_mul, abs_of_pos hα₀]
                        exact add_le_add (hGψ x) (mul_le_mul_of_nonneg_left h4 hα₀.le)
                    _ = ψ x / (1 - α) := by field_simp; ring
            have hst : ∀ n o, 0 ≤ o → ∀ x, Jgo G 0 α μ (n + 1) x o = Vgo G 0 α μ n (max x m) o :=
              fun n o ho x => hStep _ (hJgood n) o ho x
            -- geometric differences
            have hIdiff : ∀ n, (∀ o, 0 ≤ o → ∀ x, |Jgo G 0 α μ n x o - Jgo G 0 α μ (n + 1) x o| ≤ α ^ n * ψ x) →
                ∀ o, 0 ≤ o → ∀ y, |Vgo G 0 α μ n y o - Vgo G 0 α μ (n + 1) y o| ≤ α ^ (n + 1) * ψ y := by
              intro n hn o ho y
              have e : Vgo G 0 α μ n y o - Vgo G 0 α μ (n + 1) y o =
                  α * ∫ D, (Jgo G 0 α μ n (nextX y o D) (nextO o D) -
                    Jgo G 0 α μ (n + 1) (nextX y o D) (nextO o D)) ∂μ := by
                rw [integral_sub (hInt _ (hJgood n) o ho y) (hInt _ (hJgood (n + 1)) o ho y)]
                unfold Vgo
                ring
              rw [e, abs_mul, abs_of_pos hα₀, pow_succ', mul_assoc]
              refine mul_le_mul_of_nonneg_left ?_ hα₀.le
              have h1 : ‖∫ D, (Jgo G 0 α μ n (nextX y o D) (nextO o D) -
                    Jgo G 0 α μ (n + 1) (nextX y o D) (nextO o D)) ∂μ‖ ≤ (α ^ n * ψ y) * μ.real Set.univ := by
                refine norm_integral_le_of_norm_le_const ?_
                filter_upwards [hμ_nonneg] with D hD
                rw [Real.norm_eq_abs]
                refine (hn _ (hno o D ho hD) _).trans ?_
                exact mul_le_mul_of_nonneg_left (hψm (hnx y o D ho hD)) (pow_nonneg hα₀.le n)
              simpa using h1
            have hJdiff : ∀ n, ∀ o, 0 ≤ o → ∀ x,
                |Jgo G 0 α μ n x o - Jgo G 0 α μ (n + 1) x o| ≤ α ^ n * ψ x := by
              intro n
              induction n with
              | zero =>
                intro o ho x
                rw [hst 0 o ho]
                simpa [Vgo, Jgo] using hGψ x
              | succ n ih =>
                intro o ho x
                rw [hst n o ho, hst (n + 1) o ho]
                have := hIdiff n ih o ho (max x m)
                rwa [hψmax] at this
            have hVdiff : ∀ n, ∀ o, 0 ≤ o → ∀ y,
                |Vgo G 0 α μ n y o - Vgo G 0 α μ (n + 1) y o| ≤ α ^ n * ψ y := by
              intro n o ho y
              refine (hIdiff n (hJdiff n) o ho y).trans ?_
              exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hα₀.le hα₁.le (Nat.le_succ n)) (hψ0 y)
            -- general convergence lemma
            have hconv : ∀ f : ℕ → ℝ → ℝ, (∀ n x, |f n x - f (n + 1) x| ≤ α ^ n * ψ x) →
                (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (limUnder atTop (fun n => f n x)))) ∧
                ∀ B : ℝ, TendstoUniformlyOn f (fun x => limUnder atTop (fun n => f n x)) atTop
                  (Set.Iic B) := by
              intro f hf
              have hd : ∀ x n, dist (f n x) (f (n + 1) x) ≤ ψ x * α ^ n := by
                intro x n
                rw [Real.dist_eq, mul_comm]
                exact hf n x
              have ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (limUnder atTop (fun n => f n x))) :=
                fun x => (cauchySeq_of_le_geometric α (ψ x) hα₁ (hd x)).tendsto_limUnder
              refine ⟨ht, fun B => ?_⟩
              rw [Metric.tendstoUniformlyOn_iff]
              intro ε hε
              have hlim : Tendsto (fun n : ℕ => ψ B * α ^ n / (1 - α)) atTop (𝓝 0) := by
                have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα₀.le hα₁).const_mul (ψ B)).div_const (1 - α)
                simpa using this
              filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn x hx
              rw [dist_comm]
              have h1 := dist_le_of_le_geometric_of_tendsto α (ψ x) hα₁ (hd x) (ht x) n
              refine lt_of_le_of_lt (h1.trans ?_) hn
              refine div_le_div_of_nonneg_right ?_ hα'.le
              exact mul_le_mul_of_nonneg_right (hψm hx) (pow_nonneg hα₀.le n)
            have hcvx : ∀ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ), (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
                (∀ n, ConvexOn ℝ Set.univ (f n)) → ConvexOn ℝ Set.univ g := by
              intro f g hfg hf
              refine ⟨convex_univ, ?_⟩
              intro x _ y _ a b ha hb hab
              refine le_of_tendsto_of_tendsto' (hfg _) (((hfg x).const_smul a).add ((hfg y).const_smul b))
                (fun n => ?_)
              exact (hf n).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
            obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ψ m / (1 - α) := ⟨_, rfl⟩
            -- lower bound V_n
            have hVlow : ∀ n o, 0 ≤ o → ∀ y, G y - α * C ≤ Vgo G 0 α μ n y o := by
              intro n o ho y
              obtain ⟨h1, -, h3, h4⟩ := hI _ (hJgood n) o ho
              unfold Vgo
              have h5 : -C ≤ ∫ D, Jgo G 0 α μ n (nextX y o D) (nextO o D) ∂μ := by
                have h6 := h1 (min_le_left y m)
                simp only at h6
                rw [h3 _ (min_le_right y m)] at h6
                have h7 := h4 m
                rw [← hC] at h7
                linarith [(abs_le.mp h7).1]
              have := mul_le_mul_of_nonneg_left h5 hα₀.le
              linarith
            -- definitions
            refine ⟨fun x o => limUnder atTop (fun n => Jgo G 0 α μ n x o),
              fun y o => limUnder atTop (fun n => Vgo G 0 α μ n y o), ?_⟩
            intro o ho
            obtain ⟨hJt, hJu⟩ := hconv (fun n x => Jgo G 0 α μ n x o) (fun n x => hJdiff n o ho x)
            obtain ⟨hVt, hVu⟩ := hconv (fun n x => Vgo G 0 α μ n x o) (fun n x => hVdiff n o ho x)
            have hJgood' := hJgood
            rw [hGood] at hJgood'
            have hVmin : ∀ z, limUnder atTop (fun n => Vgo G 0 α μ n m o) ≤
                limUnder atTop (fun n => Vgo G 0 α μ n z o) := fun z =>
              le_of_tendsto_of_tendsto' (hVt m) (hVt z) (fun n => (hVprop _ (hJgood n) o ho).1 z)
            have hVl : ∀ y, G y - α * C ≤ limUnder atTop (fun n => Vgo G 0 α μ n y o) := fun y =>
              ge_of_tendsto' (hVt y) (fun n => hVlow n o ho y)
            have hJl : ∀ x, m ≤ x → G x - α * C ≤ limUnder atTop (fun n => Jgo G 0 α μ n x o) := by
              intro x hx
              refine ge_of_tendsto ((tendsto_add_atTop_iff_nat 1).mpr (hJt x)) (Eventually.of_forall ?_)
              intro n
              rw [hst n o ho x, max_eq_left hx]
              exact hVlow n o ho x
            have hGtop : Tendsto (fun x => G x - α * C) (cocompact ℝ) atTop :=
              tendsto_atTop_add_const_right _ (-(α * C)) hG_coercive
            refine ⟨⟨hJu, ?_, ?_⟩, ⟨hVu, ?_, ?_, ?_⟩, ?_, ?_⟩
            · exact hcvx _ _ hJt (fun n => (hJgood' n).2.2.1 o ho)
            · refine tendsto_atTop_mono' atTop ?_ (hGtop.mono_left atTop_le_cocompact)
              filter_upwards [eventually_ge_atTop m] with x hx
              exact hJl x hx
            · exact hcvx _ _ hVt (fun n => (hVprop _ (hJgood n) o ho).2.2)
            · exact tendsto_atTop_mono hVl hGtop
            · exact ⟨m, hVmin⟩
            · rw [← hm]
              refine ⟨hVmin, fun y hy => ?_⟩
              by_contra hlt'
              have hym : y < m := not_le.mp hlt'
              have h1 : ∀ n, Vgo G 0 α μ n m o + (G y - G m) ≤ Vgo G 0 α μ n y o := by
                intro n
                have h3 := (hI _ (hJgood n) o ho).2.2.1 y hym.le
                unfold Vgo
                rw [h3]
                linarith
              have h2 := le_of_tendsto_of_tendsto' ((hVt m).add_const (G y - G m)) (hVt y) h1
              have h3 := hy m
              simp only at h3
              linarith [hlt y hym]
            · intro x
              rw [← hm]
              obtain ⟨sys, hsys⟩ : ∃ sys, sys = adiSystem (L := L) (M := M) G 0 := ⟨_, rfl⟩
              rw [← hsys]
              have htr : ∀ ω k, sys.traj (sys.stationary (baseStockPolicy m) (x, o)) (x, o) ω k =
                  sys.statTraj (baseStockPolicy m) (x, o) ω k := by
                intro ω k
                induction k with
                | zero => rfl
                | succ k ih => simp only [ControlSystem.traj, ControlSystem.statTraj, ih,
                    ControlSystem.stationary]
              have hnext : ∀ s y D, sys.next s y D = (nextX y s.2 D, nextO s.2 D) := by
                intro s y D; rw [hsys]; rfl
              have hcost : ∀ s y, sys.cost s y = G y := by
                intro s y; rw [hsys]; simp [adiSystem]
              have hfeas : ∀ s y, sys.feasible s y ↔ s.1 ≤ y := by
                intro s y; rw [hsys]; rfl
              have hbsM : Measurable (baseStockPolicy m : ℝ × (Fin M → ℝ) → ℝ) :=
                measurable_fst.max measurable_const
              have hadm : sys.Admissible (sys.stationary (baseStockPolicy m) (x, o)) (x, o) := by
                refine ⟨?_, ?_, ?_⟩
                · intro k
                  have hk : Measurable (fun ω => sys.statTraj (baseStockPolicy m) (x, o) ω k) := by
                    induction k with
                    | zero => exact measurable_const
                    | succ k ih =>
                      simp only [ControlSystem.statTraj, hnext]
                      refine Measurable.prodMk ?_ ?_
                      · exact hnxM.comp (((hbsM.comp ih).prodMk ih.snd).prodMk (measurable_pi_apply k))
                      · exact hnoM.comp (((hbsM.comp ih).prodMk ih.snd).prodMk (measurable_pi_apply k))
                  exact hbsM.comp hk
                · intro k ω ω' h
                  have hk : ∀ j, j ≤ k → sys.statTraj (baseStockPolicy m) (x, o) ω j =
                      sys.statTraj (baseStockPolicy m) (x, o) ω' j := by
                    intro j
                    induction j with
                    | zero => intro _; rfl
                    | succ j ih =>
                      intro hj
                      simp only [ControlSystem.statTraj]
                      rw [ih (by omega), h j (by omega)]
                  simp only [ControlSystem.stationary]
                  rw [hk k le_rfl]
                · intro ω k
                  rw [htr, hfeas]
                  exact le_max_left _ _
              refine ⟨hadm, le_antisymm ?_ (iInf₂_le (f := fun (π : Policy ℝ (Fin (L + M + 2) → ℝ)) (_ : sys.Admissible π (x, o)) =>
                sys.discCost α μ π (x, o)) _ hadm)⟩
              refine le_iInf₂ fun π hπ => ?_
              have hae : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ k i, 0 ≤ ω k i := by
                rw [ae_all_iff]
                intro k
                exact (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) k).quasiMeasurePreserving.ae
                  hμ_nonneg
              have hpath : ∀ ω : ℕ → (Fin (L + M + 2) → ℝ), (∀ k i, 0 ≤ ω k i) → ∀ k,
                  G (baseStockPolicy m (sys.statTraj (baseStockPolicy m) (x, o) ω k)) ≤ G (π k ω) := by
                intro ω hω
                have hinv : ∀ k,
                    (sys.statTraj (baseStockPolicy m) (x, o) ω k).2 = (sys.traj π (x, o) ω k).2 ∧
                    0 ≤ (sys.traj π (x, o) ω k).2 ∧
                    (sys.statTraj (baseStockPolicy m) (x, o) ω k).1 ≤ max m (sys.traj π (x, o) ω k).1 := by
                  intro k
                  induction k with
                  | zero => exact ⟨rfl, ho, le_max_right _ _⟩
                  | succ k ih =>
                    obtain ⟨i1, i2, i3⟩ := ih
                    have hf := (hfeas _ _).mp (hπ.2.2 ω k)
                    simp only [ControlSystem.statTraj, ControlSystem.traj, hnext]
                    rw [i1]
                    refine ⟨rfl, hno _ _ i2 (hω k), ?_⟩
                    have h1 : baseStockPolicy m (sys.statTraj (baseStockPolicy m) (x, o) ω k) ≤
                        max m (π k ω) := by
                      refine max_le (i3.trans (max_le_max le_rfl hf)) (le_max_left _ _)
                    rcases le_total m (π k ω) with hc | hc
                    · rw [max_eq_right hc] at h1
                      refine le_trans ?_ (le_max_right _ _)
                      unfold nextX
                      linarith
                    · rw [max_eq_left hc] at h1
                      exact le_trans ((hnx _ _ _ i2 (hω k)).trans h1) (le_max_left _ _)
                intro k
                obtain ⟨-, -, i3⟩ := hinv k
                have hf := (hfeas _ _).mp (hπ.2.2 ω k)
                have h1 : baseStockPolicy m (sys.statTraj (baseStockPolicy m) (x, o) ω k) ≤
                    max m (π k ω) :=
                  max_le (i3.trans (max_le_max le_rfl hf)) (le_max_left _ _)
                refine (hmono _ _ (le_max_right _ _) h1).trans ?_
                rcases le_total m (π k ω) with hc | hc
                · rw [max_eq_right hc]
                · rw [max_eq_left hc]; exact hmin _
              unfold ControlSystem.discCost
              simp only [htr, hcost]
              refine EReal.sub_le_sub ?_ ?_
              · rw [EReal.coe_ennreal_le_coe_ennreal_iff]
                refine lintegral_mono_ae ?_
                filter_upwards [hae] with ω hω
                refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
                exact mul_le_mul_of_nonneg_left (hpath ω hω k) (pow_nonneg hα₀.le k)
              · rw [EReal.coe_ennreal_le_coe_ennreal_iff]
                refine lintegral_mono_ae ?_
                filter_upwards [hae] with ω hω
                refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
                exact neg_le_neg (mul_le_mul_of_nonneg_left (hpath ω hω k) (pow_nonneg hα₀.le k))
