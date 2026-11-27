-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:41:02.304055+00:00
-- url     : https://prove2.me/submissions/84fe56bf-3971-45cb-a0dc-ce97833d82d2

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 18, the verification lemma of the free lower boundary case, analytic form (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…),
p. EC-31, (192)–(195)). Let `V` be `C¹` on `(−∞, U)`, continuous on `(−∞, U]` and `C²` off a
finite set `E`, with
`V, V′, V″` bounded, `V(U) = M` and, off `E` on `(−∞, U)`,
`min{h₁ + μ₁V′ + σ₁²/2 V″, h₂ + μ₂V′ + σ₂²/2 V″, R − V} ≥ 0` (193), where `R = 0` below `U`.
Then (194) `V ≤ W` on `(−∞, U]` for the value `W` of every stopping interval policy. Moreover
(195), if a stopping interval policy `π*` attains the minimum off `E` (`V = R = 0` where it stops,
the ODE of its control where it continues), then `V` is the value of `π*` and `π*` is optimal.

Formalization Note: the expectations in (194)–(195) are replaced by the analytic value
`IsStopValue` of a stopping interval policy; the stochastic statement needs Itô's formula, which
Mathlib lacks. The printed hypothesis `V(0) = 0` (192) is dropped: the conclusions hold without it,
and the primary-system policies of Theorem 4 with a stopping level below `0` have `V(0) < 0`.
The printed `min{h(A*(x)) + …, R(A*(x)) − V(A*(x))} = 0` is read as: `V = 0` on the stopping
region of `π*` and the ODE of the control of `π*` on each of its pieces. The bounded `μ, σ, h` of
the page are constants here. The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) (V : ℝ → ℝ) (E : Finset ℝ)
    (hV1 : ContDiffOn ℝ 1 V (Set.Iio p.U)) (hVc : ContinuousOn V (Set.Iic p.U))
    (hV2 : ∀ x < p.U, x ∉ E → ContDiffAt ℝ 2 V x)
    (hbdd : ∃ B : ℝ, (∀ x < p.U, |V x| ≤ B ∧ |deriv V x| ≤ B) ∧
      ∀ x < p.U, x ∉ E → |deriv (deriv V) x| ≤ B)
    (hUM : V p.U = p.M)
    (hHJB : ∀ x < p.U, x ∉ E →
      (∀ c : Ctrl, 0 ≤ p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x) ∧
      V x ≤ 0) :
    (∀ (π : StopPolicy p) (W : ℝ → ℝ), IsStopValue p π W → ∀ x ≤ p.U, V x ≤ W x) ∧
    ∀ πs : StopPolicy p,
      (∀ x < πs.S 0, x ∉ E → V x = 0) →
      (∀ (j : Fin πs.k) (x : ℝ), x ∈ Set.Ioo (πs.S j.castSucc) (πs.S j.succ) → x ∉ E →
        p.cost (πs.ctrl j) + p.mu (πs.ctrl j) * deriv V x
          + p.sig (πs.ctrl j) ^ 2 / 2 * deriv (deriv V) x = 0) →
      IsStopValue p πs V ∧ IsStopOptimal p πs := by
        classical
        open Set Filter in
          open scoped Topology ContDiff in
            set_option maxHeartbeats 1600000 in
              have hmu (c : Ctrl) : 0 < p.mu c := by
                cases c
                · exact p.hμ₁
                · exact p.hμ₂
              have hsig (c : Ctrl) : 0 < p.sig c ^ 2 / 2 := by
                have hs : 0 < p.sig c := by
                  cases c
                  · exact p.hσ₁
                  · exact p.hσ₂
                positivity
              have hdiff (x : ℝ) (hx : x < p.U) : DifferentiableAt ℝ V x :=
                (hV1.contDiffAt (isOpen_Iio.mem_nhds hx)).differentiableAt (by norm_num)
              have hcont (x : ℝ) (hx : x < p.U) : ContinuousAt V x := (hdiff x hx).continuousAt
              have havoid (x : ℝ) : ∀ᶠ y in nhdsWithin x ({x}ᶜ), y ∉ E := by
                exact (nhdsNE_le_cofinite x) (E.finite_toSet.compl_mem_cofinite)
              have hnonpos (x : ℝ) (hx : x < p.U) : V x ≤ 0 := by
                apply le_of_tendsto (x := 𝓝[≠] x) ((hcont x hx).tendsto.mono_left nhdsWithin_le_nhds)
                filter_upwards [havoid x, nhdsWithin_le_nhds (Iio_mem_nhds hx)] with y hy hyU
                exact (hHJB y hyU hy).2
              have hsecond (f : ℝ → ℝ) (x : ℝ) (hc : ContinuousAt f x)
                  (hm : IsLocalMax f x) : deriv (deriv f) x ≤ 0 := by
                by_contra hn
                have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
                have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
                have heq : f =ᶠ[nhds x] (fun _ => f x) := by
                  filter_upwards [hm, hmin] with y hy hy'
                  exact le_antisymm hy hy'
                have hz : deriv (deriv f) x = 0 := by
                  rw [heq.deriv.deriv_eq]
                  simp
                linarith
              have hcompare : ∀ (π : StopPolicy p) (W : ℝ → ℝ), IsStopValue p π W →
                  ∀ x ≤ p.U, V x ≤ W x := by
                intro π W hW x hx
                rcases hW with ⟨hW0, hW1, hWU, hW2⟩
                have hzU : π.S 0 < p.U := by
                  rw [← π.S_last]
                  apply π.S_strictMono
                  have := π.one_le_k
                  exact Fin.mk_lt_mk.mpr (by simpa using (show 0 < π.k by omega))
                by_cases hxz : x ≤ π.S 0
                · rw [hW0 x hxz]
                  exact hnonpos x (hxz.trans_lt hzU)
                by_cases hxU : x = p.U
                · simp [hxU, hUM, hWU]
                have hxi : x ∈ Set.Ioo (π.S 0) p.U := ⟨lt_of_not_ge hxz, lt_of_le_of_ne hx hxU⟩
                by_contra hbad
                have hpos : 0 < V x - W x := sub_pos.mpr (lt_of_not_ge hbad)
                let T : Finset ℝ := E ∪ Finset.univ.image π.S
                let slopes : Finset ℝ := T.image (fun y => deriv W y - deriv V y)
                have hepsmax : 0 < (V x - W x) / (p.U - x) := div_pos hpos (sub_pos.mpr hxi.2)
                obtain ⟨ε, hε, hεnot⟩ := (Set.Ioo_infinite (a := (0 : ℝ)) (b := (V x - W x) / (p.U - x)) hepsmax).exists_notMem_finite slopes.finite_toSet
                have hε0 : 0 < ε := hε.1
                have hεsmall : ε * (p.U - x) < V x - W x := (lt_div_iff₀ (sub_pos.mpr hxi.2)).mp hε.2
                let F : ℝ → ℝ := fun y => V y - W y + ε * (y - p.U)
                have hFc : ContinuousOn F (Set.Icc (π.S 0) p.U) :=
                  ((hVc.mono (fun _ hy => hy.2)).sub hW1.continuousOn).add
                    (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
                have hFx : 0 < F x := by dsimp [F]; linarith
                have hFz : F (π.S 0) ≤ 0 := by
                  dsimp [F]
                  rw [hW0 _ le_rfl]
                  have := hnonpos (π.S 0) hzU
                  have := mul_neg_of_pos_of_neg hε0 (sub_neg.mpr hzU)
                  linarith
                have hFU : F p.U = 0 := by simp [F, hUM, hWU]
                obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hzU.le) hFc
                have hFy : 0 < F y := hFx.trans_le (hmax (Set.Ioo_subset_Icc_self hxi))
                have hyi : y ∈ Set.Ioo (π.S 0) p.U := by
                  constructor
                  · exact lt_of_le_of_ne hy.1 (by intro he; subst y; linarith)
                  · exact lt_of_le_of_ne hy.2 (by intro he; subst y; linarith)
                have hlocal : IsLocalMax F y := hmax.isLocalMax (Icc_mem_nhds hyi.1 hyi.2)
                have hdW : DifferentiableAt ℝ W y :=
                  (hW1.contDiffAt (Icc_mem_nhds hyi.1 hyi.2)).differentiableAt (by norm_num)
                have hFd : HasDerivAt F (deriv V y - deriv W y + ε) y := by
                  convert ((hdiff y hyi.2).hasDerivAt.sub hdW.hasDerivAt).add
                    (((hasDerivAt_id y).sub_const p.U).const_mul ε) using 1 <;> first | rfl | simp
                have hzero : deriv V y - deriv W y + ε = 0 := hlocal.hasDerivAt_eq_zero hFd
                have hyT : y ∉ T := by
                  intro hyt
                  apply hεnot
                  apply Finset.mem_image.mpr
                  exact ⟨y, hyt, by linarith⟩
                have hyE : y ∉ E := fun he => hyT (Finset.mem_union_left _ he)
                have hyS : ∀ i, y ≠ π.S i := by
                  intro i he
                  apply hyT
                  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
                have hpiece : ∃ j : Fin π.k, y ∈ Set.Ioo (π.S j.castSucc) (π.S j.succ) := by
                  have hex : ∃ i : Fin (π.k + 1), y < π.S i := ⟨Fin.last π.k, by simpa [π.S_last] using hyi.2⟩
                  have hne : (Finset.univ.filter (fun i => y < π.S i)).Nonempty := by
                    obtain ⟨i, hi⟩ := hex
                    exact ⟨i, by simp [hi]⟩
                  let i := Finset.min' (Finset.univ.filter (fun i => y < π.S i)) hne
                  have hi : y < π.S i := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
                  have hi0 : 0 < i.val := by
                    by_contra hn
                    have hval : i.val = 0 := by omega
                    have he : i = (0 : Fin (π.k + 1)) := Fin.ext hval
                    rw [he] at hi
                    linarith [hyi.1]
                  let j : Fin π.k := ⟨i.val - 1, by omega⟩
                  have hji : j.succ = i := Fin.ext (by dsimp [j]; omega)
                  refine ⟨j, ?_, by simpa [hji] using hi⟩
                  have hle : π.S j.castSucc ≤ y := by
                    by_contra hn
                    have hjmem : j.castSucc ∈ Finset.univ.filter (fun i => y < π.S i) := by simp [lt_of_not_ge hn]
                    have := Finset.min'_le _ _ hjmem
                    have hval := Fin.le_iff_val_le_val.mp this
                    dsimp [i, j] at hval
                    omega
                  exact lt_of_le_of_ne hle (hyS _).symm
                obtain ⟨j, hj⟩ := hpiece
                have hVyy := hV2 y hyi.2 hyE
                obtain ⟨hWyy, hWode⟩ := hW2 j y hj
                have hVd2 : DifferentiableAt ℝ (deriv V) y := (hVyy.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
                have hWd2 : DifferentiableAt ℝ (deriv W) y := (hWyy.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
                have hFderiv : deriv F =ᶠ[nhds y] (fun t => deriv V t - deriv W t + ε) := by
                  have hvnear := hVyy.eventually (by norm_num)
                  have hwnear := hWyy.eventually (by norm_num)
                  filter_upwards [hvnear, hwnear] with t htV htW
                  have hh : HasDerivAt F (deriv V t - deriv W t + ε) t := by
                    convert ((htV.differentiableAt (by norm_num)).hasDerivAt.sub
                      (htW.differentiableAt (by norm_num)).hasDerivAt).add
                      (((hasDerivAt_id t).sub_const p.U).const_mul ε) using 1 <;> first | rfl | simp
                  exact hh.deriv
                have hFsecond : deriv (deriv F) y = deriv (deriv V) y - deriv (deriv W) y := by
                  rw [hFderiv.deriv_eq]
                  simpa using ((hVd2.hasDerivAt.sub hWd2.hasDerivAt).add_const ε).deriv
                have hnon := hsecond F y (hFc.continuousAt (Icc_mem_nhds hyi.1 hyi.2)) hlocal
                rw [hFsecond] at hnon
                have hineq := (hHJB y hyi.2 hyE).1 (π.ctrl j)
                have hmul := mul_nonpos_of_nonneg_of_nonpos (hsig (π.ctrl j)).le hnon
                have hmuε := mul_pos (hmu (π.ctrl j)) hε0
                have hzeroμ : p.mu (π.ctrl j) * deriv V y - p.mu (π.ctrl j) * deriv W y +
                    p.mu (π.ctrl j) * ε = 0 := by
                  linear_combination p.mu (π.ctrl j) * hzero
                nlinarith only [hzeroμ, hineq, hWode, hmul, hmuε]
              refine ⟨hcompare, ?_⟩
              intro πs hstop hode
              have hremove (s : Set ℝ) (hs : IsOpen s) (f g : ℝ → ℝ)
                  (hf : ContinuousOn f s) (hg : ContinuousOn g s)
                  (hd : ∀ x ∈ s, x ∉ E → HasDerivAt f (g x) x) :
                  ∀ x ∈ s, HasDerivAt f (g x) x := by
                intro x hx
                have hfc := hf.continuousAt (hs.mem_nhds hx)
                have hgc := hg.continuousAt (hs.mem_nhds hx)
                have hsne : ∀ᶠ y in 𝓝[≠] x, y ∈ s := nhdsWithin_le_nhds (hs.mem_nhds hx)
                have hne : ∀ᶠ y in 𝓝[≠] x, y ∈ s ∧ y ∉ E := hsne.and (havoid x)
                have hgt : s \ (E : Set ℝ) ∈ 𝓝[>] x := nhdsGT_le_nhdsNE x hne
                have hlt : s \ (E : Set ℝ) ∈ 𝓝[<] x := nhdsLT_le_nhdsNE x hne
                have hfd : DifferentiableOn ℝ f (s \ (E : Set ℝ)) :=
                  fun y hy => (hd y hy.1 hy.2).differentiableAt.differentiableWithinAt
                have hder : ∀ᶠ y in 𝓝[≠] x, deriv f y = g y := by
                  filter_upwards [hne] with y hy
                  exact (hd y hy.1 hy.2).deriv
                have hdergt : deriv f =ᶠ[𝓝[>] x] g := nhdsGT_le_nhdsNE x hder
                have hderlt : deriv f =ᶠ[𝓝[<] x] g := nhdsLT_le_nhdsNE x hder
                have hr := hasDerivWithinAt_Ici_of_tendsto_deriv hfd hfc.continuousWithinAt hgt
                  ((hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' hdergt.symm)
                have hl := hasDerivWithinAt_Iic_of_tendsto_deriv hfd hfc.continuousWithinAt hlt
                  ((hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' hderlt.symm)
                simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
              have hsolve (a b : ℝ) (hab : a < b) (hbU : b ≤ p.U) (c : Ctrl)
                  (ho : ∀ x ∈ Ioo a b, x ∉ E →
                    p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x = 0) :
                  ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧ EqOn V G (Icc a b) := by
                let m := p.mu c
                let q := p.sig c ^ 2 / 2
                let h := p.cost c
                let r := m / q
                have hm : m ≠ 0 := (hmu c).ne'
                have hq : q ≠ 0 := (hsig c).ne'
                have hr : r ≠ 0 := div_ne_zero hm hq
                have hcV : ContinuousOn V (Icc a b) := hVc.mono (fun x hx => hx.2.trans hbU)
                have hdV : ContinuousOn (deriv V) (Ioo a b) :=
                  (hV1.continuousOn_deriv_of_isOpen isOpen_Iio le_rfl).mono
                    (fun x hx => hx.2.trans_le hbU)
                let H : ℝ → ℝ := fun x => (deriv V x + h / m) * Real.exp (r * x)
                have hcH : ContinuousOn H (Ioo a b) :=
                  (hdV.add continuousOn_const).mul (by fun_prop)
                have hdHoff : ∀ x ∈ Ioo a b, x ∉ E → HasDerivAt H 0 x := by
                  intro x hx he
                  have hd2 : DifferentiableAt ℝ (deriv V) x :=
                    ((hV2 x (hx.2.trans_le hbU) he).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
                  have hh := ((hd2.hasDerivAt.add_const (h / m)).mul
                    (((hasDerivAt_id x).const_mul r).exp))
                  have heq : deriv (deriv V) x * Real.exp (r * x) +
                      (deriv V x + h / m) * (Real.exp (r * x) * (r * 1)) = 0 := by
                    have hhode : h + m * deriv V x + q * deriv (deriv V) x = 0 := ho x hx he
                    have hz : deriv (deriv V) x + (deriv V x + h / m) * r = 0 := by
                      dsimp [r]
                      field_simp
                      nlinarith only [hhode]
                    calc
                      _ = (deriv (deriv V) x + (deriv V x + h / m) * r) * Real.exp (r * x) := by ring
                      _ = 0 := by rw [hz]; ring
                  convert hh using 1 <;> first | rfl | exact heq.symm
                have hdH := hremove (Ioo a b) isOpen_Ioo H (fun _ => 0) hcH continuousOn_const hdHoff
                let t : ℝ := (a + b) / 2
                have ht : t ∈ Ioo a b := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
                have hHconst : ∀ x ∈ Ioo a b, H x = H t := by
                  intro x hx
                  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
                    (fun y hy => (hdH y hy).differentiableAt.differentiableWithinAt)
                    (fun y hy => (hdH y hy).deriv) hx ht
                let K := H t
                have hformula : ∀ x ∈ Ioo a b, deriv V x + h / m = K * Real.exp (-r * x) := by
                  intro x hx
                  have hh := hHconst x hx
                  change (deriv V x + h / m) * Real.exp (r * x) = K at hh
                  calc
                    deriv V x + h / m = ((deriv V x + h / m) * Real.exp (r * x)) * Real.exp (-r * x) := by
                      rw [mul_assoc, ← Real.exp_add]
                      simp
                    _ = K * Real.exp (-r * x) := by rw [hh]
                let J : ℝ → ℝ := fun x => V x + h / m * x + K / r * Real.exp (-r * x)
                have hdJ : ∀ x ∈ Ioo a b, HasDerivAt J 0 x := by
                  intro x hx
                  have hh := (((hdiff x (hx.2.trans_le hbU)).hasDerivAt.add
                    ((hasDerivAt_id x).const_mul (h / m))).add
                    ((((hasDerivAt_id x).const_mul (-r)).exp).const_mul (K / r)))
                  have heq : deriv V x + h / m * 1 + K / r * (Real.exp (-r * x) * (-r * 1)) = 0 := by
                    have hhf := hformula x hx
                    calc
                      _ = deriv V x + h / m - K * Real.exp (-r * x) := by field_simp; ring
                      _ = 0 := by linarith only [hhf]
                  convert hh using 1 <;> first | rfl | exact heq.symm
                have hJconst : ∀ x ∈ Ioo a b, J x = J t := by
                  intro x hx
                  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
                    (fun y hy => (hdJ y hy).differentiableAt.differentiableWithinAt)
                    (fun y hy => (hdJ y hy).deriv) hx ht
                let G : ℝ → ℝ := fun x => J t - h / m * x - K / r * Real.exp (-r * x)
                have hG : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
                refine ⟨G, hG, ?_⟩
                have heq : EqOn V G (Ioo a b) := by
                  intro x hx
                  have hh := hJconst x hx
                  dsimp [J, G] at *
                  linarith
                apply heq.of_subset_closure hcV hG.continuous.continuousOn Ioo_subset_Icc_self
                rw [closure_Ioo hab.ne]
              have hzU : πs.S 0 < p.U := by
                rw [← πs.S_last]
                apply πs.S_strictMono
                apply Fin.mk_lt_mk.mpr
                simpa using (show 0 < πs.k by have := πs.one_le_k; omega)
              have hclosed (j : Fin πs.k) : πs.S j.castSucc < πs.S j.succ :=
                πs.S_strictMono Fin.castSucc_lt_succ
              have hupper (j : Fin πs.k) : πs.S j.succ ≤ p.U := by
                rw [← πs.S_last]
                exact πs.S_strictMono.monotone (Fin.le_last _)
              have hGs (j : Fin πs.k) := hsolve _ _ (hclosed j) (hupper j) (πs.ctrl j) (hode j)
              have hval : IsStopValue p πs V := by
                refine ⟨?_, ?_, hUM, ?_⟩
                · intro x hx
                  have hxU : x < p.U := hx.trans_lt hzU
                  have he : V =ᶠ[𝓝[<] x] (fun _ => 0) := by
                    filter_upwards [nhdsLT_le_nhdsNE x (havoid x), self_mem_nhdsWithin] with y hy hyx
                    exact hstop y (hyx.trans_le hx) hy
                  exact tendsto_nhds_unique ((hcont x hxU).tendsto.mono_left
                    (show 𝓝[<] x ≤ 𝓝 x from nhdsWithin_le_nhds)) (tendsto_const_nhds.congr' he.symm)
                · intro x hx
                  by_cases hxU : x < p.U
                  · exact (hV1.contDiffAt (isOpen_Iio.mem_nhds hxU)).contDiffWithinAt
                  · have hxU : x = p.U := le_antisymm hx.2 (le_of_not_gt hxU)
                    subst x
                    let j : Fin πs.k := ⟨πs.k - 1, by have := πs.one_le_k; omega⟩
                    have hjU : πs.S j.succ = p.U := by
                      convert πs.S_last using 1
                      congr 1
                      apply Fin.ext
                      dsimp [j]
                      have := πs.one_le_k
                      omega
                    obtain ⟨G, hG, heq⟩ := hGs j
                    have hlow : πs.S j.castSucc < p.U := by simpa [hjU] using hclosed j
                    have hnear : V =ᶠ[𝓝[Icc (πs.S 0) p.U] p.U] G := by
                      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hlow), self_mem_nhdsWithin] with y hy hyi
                      exact heq ⟨hy.le, by simpa [hjU] using hyi.2⟩
                    have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
                    exact hG1.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq hnear
                      (heq ⟨hlow.le, by rw [hjU]⟩)
                · intro j x hx
                  obtain ⟨G, hG, heq⟩ := hGs j
                  have hnear : V =ᶠ[𝓝 x] G := by
                    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
                    exact heq (Ioo_subset_Icc_self hy)
                  have hVreg : ContDiffAt ℝ 2 V x := hG.contDiffAt.congr_of_eventuallyEq hnear
                  refine ⟨hVreg, ?_⟩
                  have hcontode : ContinuousAt (fun y => p.cost (πs.ctrl j) + p.mu (πs.ctrl j) * deriv V y +
                      p.sig (πs.ctrl j) ^ 2 / 2 * deriv (deriv V) y) x := by
                    exact (continuousAt_const.add (continuousAt_const.mul
                      (hVreg.derivWithin (m := 0) (by norm_num)).continuousAt)).add
                      (continuousAt_const.mul ((hVreg.derivWithin (m := 1) (by norm_num)).derivWithin (m := 0) (by norm_num)).continuousAt)
                  apply tendsto_nhds_unique (hcontode.tendsto.mono_left (show 𝓝[≠] x ≤ 𝓝 x from nhdsWithin_le_nhds))
                    (tendsto_const_nhds.congr' ?_)
                  filter_upwards [havoid x, nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hy hyi
                  exact (hode j y hyi hy).symm
              exact ⟨hval, V, hval, hcompare⟩
