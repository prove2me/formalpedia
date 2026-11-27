-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:41:28.54571+00:00
-- url     : https://prove2.me/submissions/778b1a6f-ac44-457d-91c8-285fb7739c25

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Theorem 4 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 20–22, (25)–(27); proof pp. EC-23–EC-27). With a free lower boundary:
(a) if `h₂ > ĥ₂(h₁)` (25), there is `Ũ > 0` such that using control 1 on `[U − Ũ, U)` and
stopping on `(−∞, U − Ũ)` is optimal; (b) if `h₂ < (σ₂²/σ₁²) h₁` (26), there is `Ũ > 0` such that
using control 2 on `[U − Ũ, U)` and stopping below is optimal; (c) if
`(σ₂²/σ₁²) h₁ < h₂ < ĥ₂(h₁)` (27), there are `Ũ > S* > 0` such that using control 1 on
`[U − Ũ, U − Ũ + S*)`, control 2 on `[U − Ũ + S*, U)` and stopping below is optimal. Here
`ĥ₂(h₁) = (μ₂/μ₁) h₁ [1 + ((v₂ − v₁)/v₂) LW(−e^{−1−(−M)μ₁v₁/h₁})]` with `LW` the principal branch
of the Lambert W function.

Formalization Note: optimality is `IsStopOptimal`, over every stopping interval policy (every
stopping level, every number of intervals) with the analytic value `IsStopValue`; `Ũ` may exceed
`U` (stopping level below `0`). The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) :
    (cond25 p → ∃ (Ũ : ℝ) (hŨ : 0 < Ũ),
      IsStopOptimal p (stopOne p .one (p.U - Ũ) (by linarith))) ∧
    (cond26 p → ∃ (Ũ : ℝ) (hŨ : 0 < Ũ),
      IsStopOptimal p (stopOne p .two (p.U - Ũ) (by linarith))) ∧
    (cond27 p → ∃ (Ũ S : ℝ) (hS : 0 < S) (hSŨ : S < Ũ),
      IsStopOptimal p (stopOneTwo p (p.U - Ũ) (p.U - Ũ + S) (by linarith) (by linarith))) := by
        classical
        have finite_mono : ∀ (s : Finset ℝ) (a b : ℝ) (f : ℝ → ℝ),
            ContinuousOn f (Set.Icc a b) →
            (∀ x ∈ Set.Ioo a b, x ∉ s → DifferentiableAt ℝ f x ∧ 0 ≤ deriv f x) →
            MonotoneOn f (Set.Icc a b) := by
          intro s
          induction s using Finset.induction with
          | empty =>
            intro a b f hc hd
            apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
            · intro x hx
              rw [interior_Icc] at hx
              exact (hd x hx (by simp)).1.differentiableWithinAt
            · intro x hx
              rw [interior_Icc] at hx
              exact (hd x hx (by simp)).2
          | @insert c s hcs ih =>
            intro a b f hc hd
            have left : MonotoneOn f (Set.Icc a (min c b)) := by
              apply ih a (min c b) f (hc.mono (by intro x hx; exact ⟨hx.1, hx.2.trans (min_le_right _ _)⟩))
              intro x hx hxs
              apply hd x ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
              simp only [Finset.mem_insert, not_or]
              exact ⟨ne_of_lt (hx.2.trans_le (min_le_left _ _)), hxs⟩
            have right : MonotoneOn f (Set.Icc (max c a) b) := by
              apply ih (max c a) b f (hc.mono (by intro x hx; exact ⟨(le_max_right _ _).trans hx.1, hx.2⟩))
              intro x hx hxs
              apply hd x ⟨(le_max_right _ _).trans_lt hx.1, hx.2⟩
              simp only [Finset.mem_insert, not_or]
              exact ⟨ne_of_gt ((le_max_left _ _).trans_lt hx.1), hxs⟩
            intro x hx y hy hxy
            by_cases hxc : x ≤ c
            · by_cases hyc : y ≤ c
              · exact left ⟨hx.1, le_min hxc hx.2⟩ ⟨hy.1, le_min hyc hy.2⟩ hxy
              · have hcy : c < y := lt_of_not_ge hyc
                have hac : a ≤ c := hx.1.trans hxc
                have hcb : c ≤ b := hcy.le.trans hy.2
                exact (left ⟨hx.1, le_min hxc hx.2⟩ ⟨hac, le_min le_rfl hcb⟩ hxc).trans
                  (right ⟨max_le le_rfl hac, hcb⟩ ⟨max_le hcy.le hy.1, hy.2⟩ hcy.le)
            · have hcx : c ≤ x := (lt_of_not_ge hxc).le
              exact right ⟨max_le hcx hx.1, hx.2⟩ ⟨max_le (hcx.trans hxy) hy.1, hy.2⟩ hxy
        have hmu : ∀ c, 0 < p.mu c := by intro c; cases c; exact p.hμ₁; exact p.hμ₂
        have hsig : ∀ c, 0 < p.sig c := by intro c; cases c; exact p.hσ₁; exact p.hσ₂
        have hcost : ∀ c, 0 < p.cost c := by intro c; cases c; exact p.hh₁; exact p.hh₂
        have hvpos : ∀ c, 0 < v p c := by
          intro c
          exact div_pos (mul_pos (by norm_num) (hmu c)) (sq_pos_of_pos (hsig c))
        have hmax : ∀ c, v p c ≤ v p .two := by intro c; cases c; exact hv.le; exact le_rfl
        have maximum_principle : ∀ (a b K : ℝ) (s : Finset ℝ) (f : ℝ → ℝ),
            a < b → ContinuousOn f (Set.Icc a b) →
            (∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) →
            ContinuousOn (deriv f) (Set.Ioo a b) →
            (∀ x ∈ Set.Ioo a b, x ∉ s → DifferentiableAt ℝ (deriv f) x ∧
              ∃ q : ℝ, q ≤ K ∧ 0 ≤ deriv (deriv f) x + q * deriv f x) →
            f a ≤ 0 → f b ≤ 0 → ∀ x ∈ Set.Icc a b, f x ≤ 0 := by
          intro a b K s f hab hc hd hc' hdd ha hb x hx
          by_contra hbad
          have hfx : 0 < f x := lt_of_not_ge hbad
          have hax : a < x := lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)
          have hxb : x < b := lt_of_le_of_ne hx.2 (by intro h; subst x; linarith)
          obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_slope f hax
            (hc.mono (Set.Icc_subset_Icc le_rfl hx.2))
            (fun t ht => (hd t ⟨ht.1, ht.2.trans hxb⟩).differentiableWithinAt)
          obtain ⟨w, hw, hdw⟩ := exists_deriv_eq_slope f hxb
            (hc.mono (Set.Icc_subset_Icc hx.1 le_rfl))
            (fun t ht => (hd t ⟨hax.trans ht.1, ht.2⟩).differentiableWithinAt)
          have hdupos : 0 < deriv f u := by rw [hdu]; exact div_pos (by linarith) (sub_pos.mpr hax)
          have hdwneg : deriv f w < 0 := by rw [hdw]; exact div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hxb)
          have huw : u < w := hu.2.trans hw.1
          have hsub : Set.Icc u w ⊆ Set.Ioo a b := by intro t ht; exact ⟨hu.1.trans_le ht.1, ht.2.trans_lt hw.2⟩
          have hzero : ∃ c ∈ Set.Icc u w, deriv f c = 0 := by
            exact intermediate_value_Icc' huw.le (hc'.mono hsub) ⟨hdwneg.le, hdupos.le⟩
          let Z := Set.Icc u w ∩ {t | deriv f t = 0}
          have hZc : IsCompact Z := by
            exact isCompact_Icc.of_isClosed_subset
              ((hc'.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := (0:ℝ))))
              (by intro t ht; exact ht.1)
          obtain ⟨c, hcZ, hcmin⟩ := hZc.exists_isMinOn (by rcases hzero with ⟨c, hc, hz⟩; exact ⟨c, hc, hz⟩) continuousOn_id
          change c ∈ Set.Icc u w ∩ {t | deriv f t = 0} at hcZ
          have hcz : deriv f c = 0 := hcZ.2
          have huc : u < c := lt_of_le_of_ne hcZ.1.1 (by intro h; rw [← h] at hcz; linarith)
          have hnonneg : ∀ t ∈ Set.Icc u c, 0 ≤ deriv f t := by
            intro t ht
            by_contra hneg
            have hneg : deriv f t < 0 := lt_of_not_ge hneg
            have hut : u < t := lt_of_le_of_ne ht.1 (by intro h; subst t; linarith)
            obtain ⟨d, hdI, hdz⟩ := intermediate_value_Icc' hut.le
              (hc'.mono (by intro z hz; apply hsub; exact ⟨hz.1, hz.2.trans (ht.2.trans hcZ.1.2)⟩))
              ⟨hneg.le, hdupos.le⟩
            have hcd : c ≤ d := hcmin ⟨⟨hdI.1, hdI.2.trans (ht.2.trans hcZ.1.2)⟩, hdz⟩
            have hdt : d < t := lt_of_le_of_ne hdI.2 (by intro h; subst d; linarith)
            have htc := ht.2
            linarith
          have hG : MonotoneOn (fun t => Real.exp (K * t) * deriv f t) (Set.Icc u c) := by
            apply finite_mono s u c _
            · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
                (hc'.mono (by intro t ht; apply hsub; exact ⟨ht.1, ht.2.trans hcZ.1.2⟩))
            · intro t ht hts
              have htI : t ∈ Set.Ioo a b := hsub ⟨ht.1.le, ht.2.le.trans hcZ.1.2⟩
              obtain ⟨hdt, q, hqK, hineq⟩ := hdd t htI hts
              have he := ((hasDerivAt_id t).const_mul K).exp
              have hder := he.mul hdt.hasDerivAt
              refine ⟨hder.differentiableAt, ?_⟩
              have hde : deriv (fun t => Real.exp (K * t) * deriv f t) t =
                  Real.exp (K*t) * K * deriv f t + Real.exp (K*t) * deriv (deriv f) t := by
                simpa only [id_eq, mul_one, Pi.mul_def] using hder.deriv
              rw [hde]
              have hq : 0 ≤ (K - q) * deriv f t := mul_nonneg (sub_nonneg.mpr hqK) (hnonneg t ⟨ht.1.le, ht.2.le⟩)
              have hexp : 0 < Real.exp (K * t) := Real.exp_pos _
              nlinarith [mul_nonneg hexp.le hineq, mul_nonneg hexp.le hq]
          have hh := hG ⟨le_rfl, huc.le⟩ ⟨huc.le, le_rfl⟩ huc.le
          change Real.exp (K*u) * deriv f u ≤ Real.exp (K*c) * deriv f c at hh
          rw [hcZ.2, mul_zero] at hh
          exact (not_le_of_gt (mul_pos (Real.exp_pos _) hdupos)) hh
        have find_piece : ∀ (π : StopPolicy p) (x : ℝ), π.S 0 < x → x < p.U →
            (∀ i, π.S i ≠ x) → ∃ j : Fin π.k, x ∈ Set.Ioo (π.S j.castSucc) (π.S j.succ) := by
          intro π x h0 hU hne
          let T := Finset.univ.filter (fun i : Fin (π.k + 1) => π.S i < x)
          have hT : T.Nonempty := ⟨0, by simp [T, h0]⟩
          let i := T.max' hT
          have hi : π.S i < x := (Finset.mem_filter.mp (T.max'_mem hT)).2
          have hin : i ≠ Fin.last π.k := by intro he; rw [he, π.S_last] at hi; linarith
          obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr hin
          refine ⟨j, by simpa [hj] using hi, ?_⟩
          by_contra hn
          have hle : π.S j.succ ≤ x := le_of_not_gt hn
          have hlt : π.S j.succ < x := lt_of_le_of_ne hle (hne j.succ)
          have hm : j.succ ∈ T := by simp [T, hlt]
          have hji := T.le_max' j.succ hm
          change j.succ ≤ i at hji
          rw [← hj] at hji
          exact (not_le_of_gt (Fin.castSucc_lt_succ (i := j))) hji
        have verification : ∀ (π : StopPolicy p) (V : ℝ → ℝ) (E : Finset ℝ),
            IsStopValue p π V → ContDiffOn ℝ 1 V (Set.Iic p.U) →
            (∀ x ≤ p.U, V x ≤ 0) →
            (∀ x < p.U, x ∉ E → ContDiffAt ℝ 2 V x ∧
              ∀ c, 0 ≤ p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x) →
            IsStopOptimal p π := by
          intro π V E hV hVc hVneg hHJB
          refine ⟨V, hV, ?_⟩
          intro π' W hW x hx
          rcases hW with ⟨hWzero, hWc, hWU, hWode⟩
          have hzU : π'.S 0 < p.U := by
            rw [← π'.S_last]
            apply π'.S_strictMono
            have := π'.one_le_k
            change (0 : ℕ) < π'.k
            omega
          by_cases hxz : x ≤ π'.S 0
          · rw [hWzero x hxz]
            exact hVneg x hx
          have hxI : x ∈ Set.Icc (π'.S 0) p.U := ⟨(lt_of_not_ge hxz).le, hx⟩
          let f := fun t => V t - W t
          have hfc : ContDiffOn ℝ 1 f (Set.Icc (π'.S 0) p.U) :=
            (hVc.mono (by intro t ht; exact ht.2)).sub hWc
          have hfd : ∀ t ∈ Set.Ioo (π'.S 0) p.U, DifferentiableAt ℝ f t := by
            intro t ht
            exact (hfc.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by norm_num)
          have hfcd : ContinuousOn (deriv f) (Set.Ioo (π'.S 0) p.U) :=
            (hfc.mono Set.Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
          let D : Finset ℝ := E ∪ Finset.univ.image π'.S
          have hfdd : ∀ t ∈ Set.Ioo (π'.S 0) p.U, t ∉ D →
              DifferentiableAt ℝ (deriv f) t ∧ ∃ q ≤ v p .two,
                0 ≤ deriv (deriv f) t + q * deriv f t := by
            intro t ht htn
            have htE : t ∉ E := by intro h; exact htn (Finset.mem_union_left _ h)
            have htS : ∀ i, π'.S i ≠ t := by
              intro i hi
              apply htn
              exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
            obtain ⟨j, hj⟩ := find_piece π' t ht.1 ht.2 htS
            obtain ⟨hV2, hH⟩ := hHJB t ht.2 htE
            obtain ⟨hW2, hWeq⟩ := hWode j t hj
            have hVd := hV2.differentiableAt (by norm_num)
            have hWd := hW2.differentiableAt (by norm_num)
            have hf2 : ContDiffAt ℝ 2 f t := hV2.sub hW2
            have hfdd := (hf2.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
            refine ⟨hfdd, v p (π'.ctrl j), hmax _, ?_⟩
            have hd1 : deriv f t = deriv V t - deriv W t := by exact (hVd.hasDerivAt.sub hWd.hasDerivAt).deriv
            have hd2 : deriv (deriv f) t = deriv (deriv V) t - deriv (deriv W) t := by
              have hev : deriv f =ᶠ[nhds t] fun z => deriv V z - deriv W z := by
                have hVe := hV2.eventually (by norm_num)
                have hWe := hW2.eventually (by norm_num)
                filter_upwards [hVe, hWe] with z hzV hzW
                exact deriv_sub (hzV.differentiableAt (by norm_num)) (hzW.differentiableAt (by norm_num))
              rw [Filter.EventuallyEq.deriv_eq hev]
              exact deriv_sub ((hV2.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
                ((hW2.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
            rw [hd1, hd2, v]
            have hsq : 0 < p.sig (π'.ctrl j) ^ 2 := sq_pos_of_pos (hsig _)
            have hineq := hH (π'.ctrl j)
            apply (mul_nonneg_iff_of_pos_left hsq).mp
            rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hsq)]
            nlinarith only [hineq, hWeq]
          have hfa : f (π'.S 0) ≤ 0 := by
            dsimp [f]
            rw [hWzero _ le_rfl]
            simpa using hVneg _ hzU.le
          have hfb : f p.U ≤ 0 := by dsimp [f]; rw [hV.2.2.1, hWU]; simp
          have hresult := maximum_principle _ _ _ D f hzU hfc.continuousOn hfd hfcd hfdd hfa hfb x hxI
          dsimp [f] at hresult
          linarith
        have glue : ∀ (f g : ℝ → ℝ) (z : ℝ), ContDiff ℝ 1 f → ContDiff ℝ 1 g →
            f z = g z → deriv f z = deriv g z →
            ContDiff ℝ 1 (fun x => if x ≤ z then f x else g x) := by
          intro f g z hf hg he hd
          let H := fun x => if x ≤ z then f x else g x
          have hH : ∀ x, HasDerivAt H (if x ≤ z then deriv f x else deriv g x) x := by
            intro x
            rcases lt_trichotomy x z with h | h | h
            · rw [if_pos h.le]
              apply (hf.differentiable (by norm_num) x).hasDerivAt.congr_of_eventuallyEq
              filter_upwards [eventually_lt_nhds h] with y hy
              simp [H, hy.le]
            · subst x
              rw [if_pos le_rfl]
              have hl : HasDerivWithinAt H (deriv f z) (Set.Iic z) z :=
                (hf.differentiable (by norm_num) z).hasDerivAt.hasDerivWithinAt.congr
                  (by intro y hy; change y ≤ z at hy; simp [H, hy]) (by simp [H])
              have hr : HasDerivWithinAt H (deriv f z) (Set.Ici z) z := by
                rw [hd]
                apply (hg.differentiable (by norm_num) z).hasDerivAt.hasDerivWithinAt.congr
                · intro y hy
                  dsimp [H]
                  split_ifs with h
                  · have hyz : y = z := le_antisymm h hy
                    subst y
                    exact he
                  · rfl
                · simp [H, he]
              exact (hl.union hr).hasDerivAt (by rw [Set.Iic_union_Ici]; exact Filter.univ_mem)
            · rw [if_neg (not_le_of_gt h)]
              apply (hg.differentiable (by norm_num) x).hasDerivAt.congr_of_eventuallyEq
              filter_upwards [eventually_gt_nhds h] with y hy
              simp [H, not_le_of_gt hy]
          refine contDiff_one_iff_deriv.mpr ⟨fun x => (hH x).differentiableAt, ?_⟩
          have hcont : Continuous (fun x => if x ≤ z then deriv f x else deriv g x) :=
            (hf.continuous_deriv le_rfl).if_le (hg.continuous_deriv le_rfl)
              continuous_id continuous_const (by intro x hx; subst x; exact hd)
          have heq : deriv H = fun x => if x ≤ z then deriv f x else deriv g x := funext (fun x => (hH x).deriv)
          rwa [heq]
        let R := fun c => p.cost c / p.mu c
        have hR : ∀ c, 0 < R c := fun c => div_pos (hcost c) (hmu c)
        let F := fun c (d t : ℝ) => -R c * t + (d + R c) / v p c * (1 - Real.exp (-v p c * t))
        let F' := fun c (d t : ℝ) => -R c + (d + R c) * Real.exp (-v p c * t)
        let F'' := fun c (d t : ℝ) => -(d + R c) * v p c * Real.exp (-v p c * t)
        have hF0 : ∀ c d, F c d 0 = 0 := by intro c d; simp [F]
        have hF'0 : ∀ c d, F' c d 0 = d := by intro c d; simp [F']
        have hFs : ∀ c d, ContDiff ℝ 2 (F c d) := by intro c d; dsimp [F]; fun_prop
        have hFd : ∀ c d t, HasDerivAt (F c d) (F' c d t) t := by
          intro c d t
          have he := (((hasDerivAt_id t).const_mul (-v p c)).exp)
          have hh := ((hasDerivAt_id t).const_mul (-R c)).add
            (((hasDerivAt_const t 1).sub he).const_mul ((d + R c) / v p c))
          have heq : -R c * 1 + (d + R c) / v p c *
              (0 - Real.exp (-v p c * t) * (-v p c * 1)) = F' c d t := by
            dsimp [F']
            field_simp [(hvpos c).ne']
            <;> ring
          simp only [id_eq, Pi.add_def, Pi.sub_def] at hh
          rw [heq] at hh
          exact hh
        have hFdd : ∀ c d t, HasDerivAt (F' c d) (F'' c d t) t := by
          intro c d t
          have he := (((hasDerivAt_id t).const_mul (-v p c)).exp)
          have hh := (hasDerivAt_const t (-R c)).add (he.const_mul (d + R c))
          have heq : 0 + (d + R c) * (Real.exp (-v p c * t) * (-v p c * 1)) = F'' c d t := by
            dsimp [F'']; ring
          simp only [id_eq, Pi.add_def] at hh
          rw [heq] at hh
          exact hh
        have hnorm : ∀ c d e, p.cost c + p.mu c * d + p.sig c ^ 2 / 2 * e =
            p.sig c ^ 2 / 2 * (v p c * R c + v p c * d + e) := by
          intro c d e
          dsimp [v, R]
          field_simp [(hmu c).ne', (hsig c).ne']
          <;> ring
        have hFode : ∀ c d t, v p c * R c + v p c * F' c d t + F'' c d t = 0 := by
          intro c d t
          dsimp [F', F'']; ring
        have hFneg : ∀ c d, -R c ≤ d → d ≤ 0 → ∀ t ≥ 0, F c d t ≤ 0 := by
          intro c d hdl hdu t ht
          have hm : AntitoneOn (F c d) (Set.Ici 0) := by
            apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (hFs c d).continuous.continuousOn
            · exact (hFs c d).differentiable (by norm_num) |>.differentiableOn
            · intro x hx
              rw [(hFd c d x).deriv]
              have hxp : Real.exp (-v p c * x) ≤ 1 := Real.exp_le_one_iff.mpr (by
                rw [interior_Ici] at hx
                simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg (hvpos c).le (show 0 ≤ x from hx.le)))
              dsimp [F']
              nlinarith [mul_le_mul_of_nonneg_left hxp (by linarith : 0 ≤ d + R c)]
          simpa [hF0] using hm (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl) ht ht
        have hFroot : ∀ c d m, -R c ≤ d → d ≤ 0 → m < 0 →
            ∃ T : ℝ, 0 < T ∧ F c d T = m := by
          intro c d m hdl hdu hm
          let B := ((d + R c) / v p c - m) / R c + 1
          have hbpos : 0 < B := by
            dsimp [B]
            have hfrac : 0 ≤ (d + R c) / v p c := div_nonneg (by linarith) (hvpos c).le
            have hdiv : 0 < ((d + R c) / v p c - m) / R c := div_pos (by linarith) (hR c)
            linarith
          have hFb : F c d B < m := by
            have hcoef : 0 ≤ (d + R c) / v p c := div_nonneg (by linarith) (hvpos c).le
            have hexp : 0 ≤ Real.exp (-v p c * B) := (Real.exp_pos _).le
            have hmul := mul_nonneg hcoef hexp
            have hid : R c * B = (d + R c) / v p c - m + R c := by
              dsimp [B]
              field_simp [(hR c).ne']
              <;> ring
            dsimp [F]
            nlinarith [hR c]
          obtain ⟨T, hT, hTm⟩ := intermediate_value_Icc' hbpos.le (hFs c d).continuous.continuousOn
            (show m ∈ Set.Icc (F c d B) (F c d 0) by rw [hF0]; exact ⟨hFb.le, hm.le⟩)
          refine ⟨T, lt_of_le_of_ne hT.1 ?_, hTm⟩
          intro he
          rw [← he, hF0] at hTm
          linarith
        have branch_jet : ∀ (c : Ctrl) (d B z : ℝ) (V : ℝ → ℝ) (x : ℝ),
            V =ᶠ[nhds x] (fun y => B + F c d (y-z)) →
            ContDiffAt ℝ 2 V x ∧ deriv V x = F' c d (x-z) ∧ deriv (deriv V) x = F'' c d (x-z) := by
          intro c d B z V x he
          have hc : ContDiff ℝ 2 (fun y => B + F c d (y-z)) :=
            contDiff_const.add ((hFs c d).comp (contDiff_id.sub contDiff_const))
          have hd : deriv (fun y => B + F c d (y-z)) = fun y => F' c d (y-z) := by
            funext y
            rw [deriv_const_add, deriv_comp_sub_const, (hFd c d (y-z)).deriv]
          refine ⟨hc.contDiffAt.congr_of_eventuallyEq he, ?_, ?_⟩
          · rw [he.deriv_eq, hd]
          · rw [he.deriv.deriv_eq, hd, deriv_comp_sub_const, (hFdd c d (x-z)).deriv]
        have zero_jet : ∀ (V : ℝ → ℝ) (x : ℝ), V =ᶠ[nhds x] (fun _ => (0:ℝ)) →
            ContDiffAt ℝ 2 V x ∧ deriv V x = 0 ∧ deriv (deriv V) x = 0 := by
          intro V x he
          refine ⟨contDiffAt_const.congr_of_eventuallyEq he, ?_, ?_⟩
          · rw [he.deriv_eq]; simp
          · rw [he.deriv.deriv_eq]; simp
        have static_opt : ∀ (c : Ctrl) (T : ℝ) (hT : 0 < T), F c 0 T = p.M →
            (∀ t ∈ Set.Ioo 0 T, ∀ a, 0 ≤ v p a * R a + v p a * F' c 0 t + F'' c 0 t) →
            IsStopOptimal p (stopOne p c (p.U-T) (by linarith)) := by
          intro c T hT hTM hres
          let z := p.U-T
          let V := fun x => if x ≤ z then (0:ℝ) else F c 0 (x-z)
          have hVz : V z = 0 := by simp [V]
          have hVc : ContDiff ℝ 1 V := by
            apply glue (fun _ => 0) (fun x => F c 0 (x-z)) z contDiff_const
              (((hFs c 0).of_le (by norm_num)).comp (contDiff_id.sub contDiff_const))
            · simp [hF0]
            · rw [deriv_const, deriv_comp_sub_const, (hFd c 0 (z-z)).deriv]
              simp [hF'0]
          have hVneg : ∀ x ≤ p.U, V x ≤ 0 := by
            intro x hx
            dsimp [V]
            split_ifs with h
            · exact le_rfl
            · exact hFneg c 0 (by linarith [hR c]) le_rfl (x-z) (by linarith)
          have hVright : ∀ x, z < x → ContDiffAt ℝ 2 V x ∧
              deriv V x = F' c 0 (x-z) ∧ deriv (deriv V) x = F'' c 0 (x-z) := by
            intro x hx
            apply branch_jet c 0 0 z V x
            filter_upwards [eventually_gt_nhds hx] with y hy
            simp [V, not_le_of_gt hy]
          have hVleft : ∀ x, x < z → ContDiffAt ℝ 2 V x ∧ deriv V x = 0 ∧ deriv (deriv V) x = 0 := by
            intro x hx
            apply zero_jet V x
            filter_upwards [eventually_lt_nhds hx] with y hy
            simp [V, hy.le]
          have hVU : V p.U = p.M := by
            have hzU : z < p.U := by dsimp [z]; linarith
            simp only [V, if_neg (not_le_of_gt hzU)]
            have he : p.U-z = T := by dsimp [z]; ring
            rw [he, hTM]
          have hVal : IsStopValue p (stopOne p c (p.U-T) (by linarith)) V := by
            refine ⟨?_, hVc.contDiffOn, hVU, ?_⟩
            · intro x hx
              change x ≤ z at hx
              simp [V, hx]
            · intro j x hx
              fin_cases j
              change x ∈ Set.Ioo z p.U at hx
              obtain ⟨hc2, hd1, hd2⟩ := hVright x hx.1
              refine ⟨hc2, ?_⟩
              change p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x = 0
              rw [hnorm, hd1, hd2, hFode, mul_zero]
          apply verification _ V {z} hVal hVc.contDiffOn hVneg
          intro x hx hxn
          have hxz : x ≠ z := by simpa using hxn
          rcases lt_or_gt_of_ne hxz with h | h
          · obtain ⟨hc2, hd1, hd2⟩ := hVleft x h
            refine ⟨hc2, ?_⟩
            intro a
            rw [hd1, hd2]
            simpa using (hcost a).le
          · obtain ⟨hc2, hd1, hd2⟩ := hVright x h
            refine ⟨hc2, ?_⟩
            intro a
            rw [hnorm, hd1, hd2]
            apply mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
            apply hres (x-z) ⟨sub_pos.mpr h, ?_⟩ a
            dsimp [z]
            linarith
        have hRv : ∀ c, v p c * R c = 2 * p.cost c / p.sig c ^ 2 := by
          intro c
          dsimp [v, R]
          field_simp [(hmu c).ne']
          <;> ring
        have h26norm : cond26 p → v p .two * R .two < v p .one * R .one := by
          intro h
          have hs1 : 0 < p.σ₁ ^ 2 := sq_pos_of_pos p.hσ₁
          have hs2 : 0 < p.σ₂ ^ 2 := sq_pos_of_pos p.hσ₂
          have hh := mul_lt_mul_of_pos_right h hs1
          have he : p.σ₂ ^ 2 / p.σ₁ ^ 2 * p.h₁ * p.σ₁ ^ 2 = p.σ₂ ^ 2 * p.h₁ := by
            field_simp [hs1.ne', p.hσ₁.ne']
          change p.h₂ * p.σ₁ ^ 2 < p.σ₂ ^ 2 / p.σ₁ ^ 2 * p.h₁ * p.σ₁ ^ 2 at hh
          rw [he] at hh
          rw [hRv, hRv]
          apply (div_lt_div_iff₀ hs2 hs1).mpr
          change 2 * p.h₂ * p.σ₁ ^ 2 < 2 * p.h₁ * p.σ₂ ^ 2
          nlinarith only [hh]
        have case26 : cond26 p → ∃ (T : ℝ) (hT : 0 < T),
            IsStopOptimal p (stopOne p .two (p.U-T) (by linarith)) := by
          intro h
          obtain ⟨T, hT, hTM⟩ := hFroot .two 0 p.M (by linarith [hR .two]) le_rfl p.hM
          refine ⟨T, hT, static_opt .two T hT hTM ?_⟩
          intro t ht a
          cases a with
          | two => rw [hFode]
          | one =>
            have he : Real.exp (-v p .two * t) ≤ 1 := Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hvpos .two).le) ht.1.le)
            have hterm := mul_nonneg (mul_nonneg (sub_pos.mpr hv).le (hR .two).le) (sub_nonneg.mpr he)
            have hh := h26norm h
            dsimp [F', F'']
            nlinarith only [hterm, hh]
        have hWmono : StrictMonoOn (fun y : ℝ => y * Real.exp y) (Set.Ici (-1)) := by
          apply strictMonoOn_of_deriv_pos (convex_Ici (-1))
            ((continuous_id.mul Real.continuous_exp).continuousOn)
          intro y hy
          rw [interior_Ici] at hy
          have hd := (hasDerivAt_id y).mul (Real.hasDerivAt_exp y)
          have hdv : deriv (fun y : ℝ => y * Real.exp y) y = Real.exp y + y * Real.exp y := by
            simpa only [Pi.mul_def, id_eq, one_mul] using hd.deriv
          simp only [Pi.mul_def, id_eq]
          rw [hdv]
          have hy' : -1 < y := hy
          have he := mul_pos (show 0 < 1+y by linarith only [hy']) (Real.exp_pos y)
          nlinarith only [he]
        have hWinv : ∀ y : ℝ, -1 ≤ y → LiquidWelfareFPA.lambertW (y * Real.exp y) = y := by
          intro y hy
          have hex : ∃ z : ℝ, -1 ≤ z ∧ z * Real.exp z = y * Real.exp y := ⟨y, hy, rfl⟩
          rw [LiquidWelfareFPA.lambertW, dif_pos hex]
          have hs := Classical.choose_spec hex
          exact hWmono.injOn hs.1 hy hs.2
        obtain ⟨T₁, hT₁, hT₁M⟩ := hFroot .one 0 p.M (by linarith [hR .one]) le_rfl p.hM
        let e₁ := Real.exp (-v p .one * T₁)
        have he₁pos : 0 < e₁ := Real.exp_pos _
        have he₁lt : e₁ < 1 := Real.exp_lt_one_iff.mpr
          (mul_neg_of_neg_of_pos (neg_neg_of_pos (hvpos .one)) hT₁)
        have harg : -1 - (-p.M) * p.μ₁ * v p .one / p.h₁ = -v p .one * T₁ - e₁ := by
          have hh := hT₁M
          dsimp [F, R, Params.cost, Params.mu] at hh
          change -(p.h₁ / p.μ₁) * T₁ + (0 + p.h₁ / p.μ₁) / v p .one * (1-e₁) = p.M at hh
          field_simp [p.hμ₁.ne', (hvpos .one).ne'] at hh
          apply (mul_right_inj' p.hh₁.ne').mp
          field_simp [p.hh₁.ne']
          nlinarith only [hh]
        have hLW : LiquidWelfareFPA.lambertW
            (-Real.exp (-1 - (-p.M) * p.μ₁ * v p .one / p.h₁)) = -e₁ := by
          rw [harg, Real.exp_sub]
          have heq : -(Real.exp (-v p .one * T₁) / Real.exp e₁) = (-e₁) * Real.exp (-e₁) := by
            dsimp [e₁]
            rw [Real.exp_neg]
            ring
          rw [heq]
          exact hWinv (-e₁) (by linarith)
        have hupper : upperCurve p p.h₁ = p.μ₂ * R .one *
            (1 - (v p .two - v p .one) / v p .two * e₁) := by
          rw [upperCurve, hLW]
          dsimp [R, Params.cost, Params.mu]
          ring
        let Q := v p .two * R .two - v p .two * R .one +
          (v p .two - v p .one) * R .one * e₁
        have hQ : Q = v p .two / p.μ₂ * (p.h₂ - upperCurve p p.h₁) := by
          rw [hupper]
          dsimp [Q, R, Params.cost, Params.mu]
          field_simp [p.hμ₁.ne', p.hμ₂.ne', (hvpos .two).ne']
          <;> ring
        have case25 : cond25 p → ∃ (T : ℝ) (hT : 0 < T),
            IsStopOptimal p (stopOne p .one (p.U-T) (by linarith)) := by
          intro h
          have hQpos : 0 < Q := by
            rw [hQ]
            exact mul_pos (div_pos (hvpos .two) p.hμ₂) (sub_pos.mpr h)
          refine ⟨T₁, hT₁, static_opt .one T₁ hT₁ hT₁M ?_⟩
          intro t ht a
          cases a with
          | one => rw [hFode]
          | two =>
            have he : e₁ ≤ Real.exp (-v p .one * t) := by
              apply Real.exp_le_exp.mpr
              exact mul_le_mul_of_nonpos_left ht.2.le (neg_nonpos.mpr (hvpos .one).le)
            have hterm := mul_nonneg (mul_nonneg (sub_pos.mpr hv).le (hR .one).le) (sub_nonneg.mpr he)
            dsimp [F', F'']
            dsimp [Q] at hQpos
            nlinarith only [hterm, hQpos]
        have h27norm : cond27 p → v p .one * R .one < v p .two * R .two ∧ Q < 0 := by
          intro h
          constructor
          · have hs1 : 0 < p.σ₁ ^ 2 := sq_pos_of_pos p.hσ₁
            have hs2 : 0 < p.σ₂ ^ 2 := sq_pos_of_pos p.hσ₂
            have hh := mul_lt_mul_of_pos_right h.1 hs1
            have he : p.σ₂ ^ 2 / p.σ₁ ^ 2 * p.h₁ * p.σ₁ ^ 2 = p.σ₂ ^ 2 * p.h₁ := by
              field_simp [p.hσ₁.ne']
            rw [he] at hh
            rw [hRv, hRv]
            apply (div_lt_div_iff₀ hs1 hs2).mpr
            change 2 * p.h₁ * p.σ₂ ^ 2 < 2 * p.h₂ * p.σ₁ ^ 2
            nlinarith only [hh]
          · rw [hQ]
            exact mul_neg_of_pos_of_neg (div_pos (hvpos .two) p.hμ₂) (sub_neg.mpr h.2)
        have hFstrict : ∀ c, StrictAntiOn (F c 0) (Set.Ici 0) := by
          intro c
          apply strictAntiOn_of_deriv_neg (convex_Ici 0) (hFs c 0).continuous.continuousOn
          intro t ht
          rw [interior_Ici] at ht
          rw [(hFd c 0 t).deriv]
          have he : Real.exp (-v p c * t) < 1 := Real.exp_lt_one_iff.mpr
            (mul_neg_of_neg_of_pos (neg_neg_of_pos (hvpos c)) ht)
          have hh := mul_pos (hR c) (sub_pos.mpr he)
          dsimp [F']
          nlinarith only [hh]
        refine ⟨case25, case26, ?_⟩
        intro h27
        obtain ⟨hlow, hhigh⟩ := h27norm h27
        let w := (v p .two * R .one - v p .two * R .two) / ((v p .two - v p .one) * R .one)
        have hden : 0 < (v p .two - v p .one) * R .one := mul_pos (sub_pos.mpr hv) (hR .one)
        have hwdef : (v p .two - v p .one) * R .one * w = v p .two * R .one - v p .two * R .two := by
          dsimp [w]
          exact mul_div_cancel₀ _ hden.ne'
        have hew : e₁ < w := by
          apply (mul_lt_mul_iff_right₀ hden).mp
          dsimp [Q] at hhigh
          nlinarith only [hwdef, hhigh]
        have hwpos : 0 < w := he₁pos.trans hew
        have hwlt : w < 1 := by
          apply (mul_lt_mul_iff_right₀ hden).mp
          nlinarith only [hwdef, hlow]
        let S := -Real.log w / v p .one
        have hS : 0 < S := div_pos (neg_pos.mpr (Real.log_neg hwpos hwlt)) (hvpos .one)
        have hES : Real.exp (-v p .one * S) = w := by
          have he : -v p .one * S = Real.log w := by
            dsimp [S]
            field_simp [(hvpos .one).ne']
          rw [he, Real.exp_log hwpos]
        have hST : S < T₁ := by
          have hh : -v p .one * T₁ < -v p .one * S := Real.exp_lt_exp.mp (by rw [hES]; exact hew)
          nlinarith only [hh, hvpos .one]
        have hSM : p.M < F .one 0 S := by
          rw [← hT₁M]
          exact hFstrict .one (Set.mem_Ici.mpr hS.le) (Set.mem_Ici.mpr hT₁.le) hST
        have hSneg : F .one 0 S < 0 := by
          simpa only [hF0] using hFstrict .one (Set.mem_Ici.mpr (le_rfl : (0:ℝ) ≤ 0)) (Set.mem_Ici.mpr hS.le) hS
        let d := F' .one 0 S
        have hddef : d = -R .one + R .one * w := by dsimp [d, F']; rw [hES]; simp
        have hdneg : d < 0 := by
          have hh := mul_pos (hR .one) (sub_pos.mpr hwlt)
          rw [hddef]
          nlinarith only [hh]
        have hdp : 0 < d + R .one := by rw [hddef]; nlinarith only [mul_pos (hR .one) hwpos]
        have hswitch : v p .one * R .one - v p .two * R .two + (v p .one-v p .two)*d = 0 := by
          rw [hddef]
          nlinarith only [hwdef]
        have hdr2 : -R .two < d := by
          have hh : v p .two * (d+R .two) = v p .one * (d+R .one) := by nlinarith only [hswitch]
          have hp : 0 < v p .two * (d+R .two) := by rw [hh]; exact mul_pos (hvpos .one) hdp
          have hp' := (mul_pos_iff_of_pos_left (hvpos .two)).mp hp
          linarith
        obtain ⟨L, hL, hLM⟩ := hFroot .two d (p.M - F .one 0 S) hdr2.le hdneg.le (sub_neg.mpr hSM)
        let T := S+L
        have hT : 0 < T := add_pos hS hL
        have hST' : S < T := by dsimp [T]; linarith
        have hres1 : ∀ t ∈ Set.Ioo 0 S, ∀ a, 0 ≤ v p a * R a + v p a * F' .one 0 t + F'' .one 0 t := by
          intro t ht a
          cases a with
          | one => rw [hFode]
          | two =>
            have he : w ≤ Real.exp (-v p .one * t) := by
              rw [← hES]
              apply Real.exp_le_exp.mpr
              exact mul_le_mul_of_nonpos_left ht.2.le (neg_nonpos.mpr (hvpos .one).le)
            have hh := mul_nonneg hden.le (sub_nonneg.mpr he)
            dsimp [F', F'']
            nlinarith only [hh, hwdef]
        have hres2 : ∀ t ≥ 0, ∀ a, 0 ≤ v p a * R a + v p a * F' .two d t + F'' .two d t := by
          intro t ht a
          cases a with
          | two => rw [hFode]
          | one =>
            have he : Real.exp (-v p .two * t) ≤ 1 := Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hvpos .two).le) ht)
            have hdt : F' .two d t ≤ d := by
              dsimp [F']
              nlinarith only [mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ d+R .two)]
            have hh := mul_nonneg (sub_pos.mpr hv).le (sub_nonneg.mpr hdt)
            have ho := hFode .two d t
            nlinarith only [hh, ho, hswitch]
        let z := p.U-T
        let s := z+S
        have hzs : z < s := by dsimp [s]; linarith
        have hsU : s < p.U := by dsimp [s, z]; linarith
        let G₁ := fun x => F .one 0 (x-z)
        let G₂ := fun x => F .one 0 S + F .two d (x-s)
        let G := fun x => if x ≤ s then G₁ x else G₂ x
        have hG₁c : ContDiff ℝ 1 G₁ :=
          ((hFs .one 0).of_le (by norm_num)).comp (contDiff_id.sub contDiff_const)
        have hG₂c : ContDiff ℝ 1 G₂ :=
          contDiff_const.add (((hFs .two d).of_le (by norm_num)).comp (contDiff_id.sub contDiff_const))
        have hsz : s-z = S := by dsimp [s]; ring
        have hGc : ContDiff ℝ 1 G := by
          apply glue G₁ G₂ s hG₁c hG₂c
          · dsimp [G₁, G₂]
            rw [hsz, sub_self, hF0, add_zero]
          · dsimp [G₁, G₂]
            rw [deriv_const_add, deriv_comp_sub_const, deriv_comp_sub_const,
              (hFd .one 0 (s-z)).deriv, (hFd .two d (s-s)).deriv]
            rw [hsz, sub_self, hF'0]
        have hGz : G z = 0 := by simp [G, hzs.le, G₁, hF0]
        have hGdz : deriv G z = 0 := by
          have hh : G =ᶠ[nhds z] (fun x => (0:ℝ) + F .one 0 (x-z)) := by
            filter_upwards [eventually_lt_nhds hzs] with y hy
            simp [G, G₁, hy.le]
          have hj := (branch_jet .one 0 0 z G z hh).2.1
          simpa [hF'0] using hj
        let V := fun x => if x ≤ z then (0:ℝ) else G x
        have hVc : ContDiff ℝ 1 V :=
          glue (fun _ => 0) G z contDiff_const hGc hGz.symm (by simpa using hGdz.symm)
        have hVleft : ∀ x, x < z → ContDiffAt ℝ 2 V x ∧ deriv V x = 0 ∧ deriv (deriv V) x = 0 := by
          intro x hx
          apply zero_jet V x
          filter_upwards [eventually_lt_nhds hx] with y hy
          simp [V, hy.le]
        have hVmid : ∀ x, z < x → x < s → ContDiffAt ℝ 2 V x ∧
            deriv V x = F' .one 0 (x-z) ∧ deriv (deriv V) x = F'' .one 0 (x-z) := by
          intro x hzx hxs
          apply branch_jet .one 0 0 z V x
          filter_upwards [eventually_gt_nhds hzx, eventually_lt_nhds hxs] with y hyz hys
          simp [V, G, G₁, not_le_of_gt hyz, hys.le]
        have hVright : ∀ x, s < x → ContDiffAt ℝ 2 V x ∧
            deriv V x = F' .two d (x-s) ∧ deriv (deriv V) x = F'' .two d (x-s) := by
          intro x hsx
          apply branch_jet .two d (F .one 0 S) s V x
          filter_upwards [eventually_gt_nhds hsx] with y hys
          simp [V, G, G₂, not_le_of_gt hys, not_le_of_gt (hzs.trans hys)]
        have hVU : V p.U = p.M := by
          have hUs : p.U-s = L := by dsimp [s, z, T]; ring
          dsimp [V, G]
          rw [if_neg (not_le_of_gt (hzs.trans hsU)), if_neg (not_le_of_gt hsU)]
          dsimp [G₂]
          rw [hUs, hLM]
          ring
        have hVneg : ∀ x ≤ p.U, V x ≤ 0 := by
          intro x hx
          dsimp [V, G]
          split_ifs with hxz hxs
          · exact le_rfl
          · exact hFneg .one 0 (by linarith [hR .one]) le_rfl (x-z) (by linarith)
          · have hh := hFneg .two d hdr2.le hdneg.le (x-s) (by linarith)
            dsimp [G₂]
            linarith
        have hVal : IsStopValue p (stopOneTwo p (p.U-T) (p.U-T+S) (by linarith) (by linarith)) V := by
          refine ⟨?_, hVc.contDiffOn, hVU, ?_⟩
          · intro x hx
            change x ≤ z at hx
            simp [V, hx]
          · intro j x hx
            fin_cases j
            · change x ∈ Set.Ioo z s at hx
              obtain ⟨hc2, hd1, hd2⟩ := hVmid x hx.1 hx.2
              refine ⟨hc2, ?_⟩
              change p.cost .one + p.mu .one * deriv V x + p.sig .one ^ 2 / 2 * deriv (deriv V) x = 0
              rw [hnorm, hd1, hd2, hFode, mul_zero]
            · change x ∈ Set.Ioo s p.U at hx
              obtain ⟨hc2, hd1, hd2⟩ := hVright x hx.1
              refine ⟨hc2, ?_⟩
              change p.cost .two + p.mu .two * deriv V x + p.sig .two ^ 2 / 2 * deriv (deriv V) x = 0
              rw [hnorm, hd1, hd2, hFode, mul_zero]
        refine ⟨T, S, hS, hST', ?_⟩
        apply verification _ V {z,s} hVal hVc.contDiffOn hVneg
        intro x hx hxn
        have hxz : x ≠ z := by intro h; apply hxn; simp [h]
        have hxs : x ≠ s := by intro h; apply hxn; simp [h]
        rcases lt_or_gt_of_ne hxz with h | h
        · obtain ⟨hc2, hd1, hd2⟩ := hVleft x h
          refine ⟨hc2, ?_⟩
          intro a
          rw [hd1, hd2]
          simpa using (hcost a).le
        · rcases lt_or_gt_of_ne hxs with h' | h'
          · obtain ⟨hc2, hd1, hd2⟩ := hVmid x h h'
            refine ⟨hc2, ?_⟩
            intro a
            rw [hnorm, hd1, hd2]
            apply mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
            apply hres1 (x-z) ⟨sub_pos.mpr h, ?_⟩ a
            dsimp [s] at h'
            linarith
          · obtain ⟨hc2, hd1, hd2⟩ := hVright x h'
            refine ⟨hc2, ?_⟩
            intro a
            rw [hnorm, hd1, hd2]
            apply mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
            exact hres2 (x-s) (sub_nonneg.mpr h'.le) a
