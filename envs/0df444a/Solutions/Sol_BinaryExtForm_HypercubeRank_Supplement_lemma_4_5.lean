-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.Supplement.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:24.506886+00:00
-- url     : https://prove2.me/submissions/f8a9ba36-e3fe-489d-b789-969dac025c24

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

open BinaryExtForm
open BinaryExtForm.HypercubeRank
open BinaryExtForm.HypercubeRank.Supplement

open BinaryExtForm.HypercubeRank
theorem solution {d k ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B)
    (hN : IsNatural B) (α : Fin ℓ → ℤ) (f : Fin ℓ → ℝ)
    (hf : ∀ j, (α j : ℝ) < f j ∧ f j < α j + 1) :
    let S : Set (Fin (d + 1) → ℝ) := ⋃ j, Set.extremePoints ℝ (slice B (f j))
    (∀ s ∈ S, ∃ u v, Hirsch.Adj B u v ∧ s ∈ openSegment ℝ u v) ∧
    (∀ s ∈ Set.extremePoints ℝ (convexHull ℝ S),
      ∃ u v, Hirsch.Adj B u v ∧ s ∈ openSegment ℝ u v) ∧
    ∀ u v, Hirsch.Adj B u v →
      ((∃ s ∈ S, s ∈ openSegment ℝ u v) ↔
        (∃ s ∈ Set.extremePoints ℝ (convexHull ℝ S), s ∈ openSegment ℝ u v)) := by
          intro S
          obtain ⟨hpoly, -, -, -⟩ := hB
          obtain ⟨V, hV⟩ := hpoly
          have hconv : Convex ℝ B := hV ▸ convex_convexHull ℝ _
          have hcomp : IsCompact B := hV ▸ Set.Finite.isCompact_convexHull ℝ V.finite_toSet
          have key : ∀ g : ℝ, (∀ p ∈ Set.extremePoints ℝ B, p 0 ≠ g) →
              ∀ s ∈ Set.extremePoints ℝ (slice B g), ∃ u v, Hirsch.Adj B u v ∧ s ∈ openSegment ℝ u v := by
            intro g hg s hs
            obtain ⟨⟨hsB, hs0⟩, hsl⟩ := hs
            have interval : ∀ (x δ : Fin (d+1) → ℝ) (r1 r2 : ℝ), 0 < r1 + r2 → x + r1 • δ ∈ B →
                x + (-r2) • δ ∈ B → ∀ t, -r2 ≤ t → t ≤ r1 → x + t • δ ∈ B := by
              intro x δ r1 r2 hr h1 h2 t ht1 ht2
              have := hconv h1 h2 (a := (t + r2)/(r1+r2)) (b := (r1 - t)/(r1+r2))
                (div_nonneg (by linarith) hr.le) (div_nonneg (by linarith) hr.le) (by field_simp; ring)
              convert this using 1
              ext i
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              field_simp
              ring
            have hnotext : s ∉ Set.extremePoints ℝ B := fun h => hg s h hs0
            rw [mem_extremePoints] at hnotext
            push_neg at hnotext
            obtain ⟨a, ha, b, hb, hsab, hne⟩ := hnotext hsB
            obtain ⟨p, q, hp, hq, hpq, hs_eq⟩ := hsab
            set e := b - a with he
            have ha' : a = s + (-q) • e := by
              rw [← hs_eq, he]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
              rw [show p = 1 - q by linarith]; ring
            have hb' : b = s + p • e := by
              rw [← hs_eq, he]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
              rw [show p = 1 - q by linarith]; ring
            have he0 : e 0 ≠ 0 := by
              intro h0
              have ha0 : a 0 = g := by rw [ha']; simp [h0, hs0]
              have hb0 : b 0 = g := by rw [hb']; simp [h0, hs0]
              have h1 := hsl ⟨ha, ha0⟩ ⟨hb, hb0⟩ ⟨p, q, hp, hq, hpq, hs_eq⟩
              have h2 := hsl ⟨hb, hb0⟩ ⟨ha, ha0⟩ ⟨q, p, hq, hp, by linarith, (add_comm _ _).trans hs_eq⟩
              exact hne h1 h2
            let Dm : (Fin (d+1) → ℝ) → Prop := fun δ => ∃ ε > 0, ∀ t : ℝ, |t| ≤ ε → s + t • δ ∈ B
            have hDe : Dm e := by
              refine ⟨min p q, lt_min hp hq, fun t ht => ?_⟩
              rw [abs_le] at ht
              exact interval s e p q (by linarith) (hb' ▸ hb) (ha' ▸ ha) t
                (by linarith [min_le_right p q]) (by linarith [min_le_left p q])
            have hDsmul : ∀ δ (c : ℝ), Dm δ → Dm (c • δ) := by
              rintro δ c ⟨ε, hε, hδ⟩
              refine ⟨ε / (|c| + 1), by positivity, fun t ht => ?_⟩
              rw [smul_smul]
              apply hδ
              rw [abs_mul]
              have h1 : |t| * (|c| + 1) ≤ ε := by
                rw [le_div_iff₀ (by positivity)] at ht; exact ht
              nlinarith [abs_nonneg t, abs_nonneg c]
            have hDadd : ∀ δ1 δ2 : Fin (d+1) → ℝ, Dm δ1 → Dm δ2 → Dm (δ1 + δ2) := by
              rintro δ1 δ2 ⟨ε1, hε1, h1⟩ ⟨ε2, hε2, h2⟩
              refine ⟨min ε1 ε2 / 2, by positivity, fun t ht => ?_⟩
              have k1 := h1 (2 * t) (by rw [abs_mul]; norm_num; linarith [min_le_left ε1 ε2])
              have k2 := h2 (2 * t) (by rw [abs_mul]; norm_num; linarith [min_le_right ε1 ε2])
              have := hconv k1 k2 (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
              convert this using 1
              ext i
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              ring
            have par : ∀ δ : Fin (d+1) → ℝ, Dm δ → δ = (δ 0 / e 0) • e := by
              intro δ hδ
              have hγ := hDadd _ _ hδ (hDsmul e (-(δ 0 / e 0)) hDe)
              obtain ⟨ε, hε, hγ⟩ := hγ
              set γ := δ + (-(δ 0 / e 0)) • e with hγdef
              have hγ0 : γ 0 = 0 := by
                simp only [hγdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring
              have k1 := hγ ε (by rw [abs_of_pos hε])
              have k2 := hγ (-ε) (by rw [abs_neg, abs_of_pos hε])
              have := hsl (x₁ := s + ε • γ) (x₂ := s + (-ε) • γ) ⟨k1, by simp [hγ0, hs0]⟩
                ⟨k2, by simp [hγ0, hs0]⟩ ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
                  ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
              have hz : ε • γ = 0 := by
                have h2 : s + ε • γ - s = 0 := by rw [this]; simp
                simpa using h2
              have hγz : γ = 0 := by
                rcases smul_eq_zero.mp hz with h | h
                · exact absurd h hε.ne'
                · exact h
              have : δ = γ + (δ 0 / e 0) • e := by rw [hγdef]; simp
              conv_lhs => rw [this, hγz, zero_add]
            let T : Set ℝ := {t | s + t • e ∈ B}
            have hTc : IsCompact T := by
              apply Metric.isCompact_of_isClosed_isBounded
              · exact hcomp.isClosed.preimage (by fun_prop)
              · apply ((hcomp.image (f := fun x : Fin (d+1) → ℝ => (x 0 - s 0) / e 0) (by fun_prop)).isBounded).subset
                intro t ht
                refine ⟨s + t • e, ht, ?_⟩
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                field_simp; ring
            have hqT : -q ∈ T := by show s + (-q) • e ∈ B; rw [← ha']; exact ha
            have hpT : p ∈ T := by show s + p • e ∈ B; rw [← hb']; exact hb
            have hTne : T.Nonempty := ⟨p, hpT⟩
            set t1 := sInf T with ht1
            set t2 := sSup T with ht2
            have ht1T : t1 ∈ T := hTc.sInf_mem hTne
            have ht2T : t2 ∈ T := hTc.sSup_mem hTne
            have hT1 : ∀ t ∈ T, t1 ≤ t := fun t ht => csInf_le hTc.bddBelow ht
            have hT2 : ∀ t ∈ T, t ≤ t2 := fun t ht => le_csSup hTc.bddAbove ht
            have ht1n : t1 < 0 := by linarith [hT1 _ hqT]
            have ht2p : 0 < t2 := by linarith [hT2 _ hpT]
            have hne21 : t2 - t1 ≠ 0 := (by linarith : (0:ℝ) < t2 - t1).ne'
            set u := s + t1 • e with hu
            set v := s + t2 • e with hv
            have huB : u ∈ B := ht1T
            have hvB : v ∈ B := ht2T
            have seg1 : ∀ σ, t1 ≤ σ → σ ≤ t2 → s + σ • e ∈ segment ℝ u v := by
              intro σ h1 h2
              refine ⟨(t2 - σ)/(t2 - t1), (σ - t1)/(t2 - t1), div_nonneg (by linarith) (by linarith),
                div_nonneg (by linarith) (by linarith), by field_simp; ring, ?_⟩
              ext i
              simp only [hu, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              field_simp; ring
            have seg2 : ∀ z ∈ segment ℝ u v, ∃ τ, t1 ≤ τ ∧ τ ≤ t2 ∧ z = s + τ • e := by
              rintro z ⟨a', b', ha', hb', hab', rfl⟩
              refine ⟨a' * t1 + b' * t2, by nlinarith, by nlinarith, ?_⟩
              ext i
              simp only [hu, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rw [show a' = 1 - b' by linarith]; ring
            have huv : u ≠ v := by
              intro h
              have := congrFun h 0
              simp only [hu, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
              have : (t1 - t2) * e 0 = 0 := by linarith
              rcases mul_eq_zero.mp this with h | h
              · linarith
              · exact he0 h
            have hsuv : s ∈ openSegment ℝ u v := by
              refine ⟨t2/(t2 - t1), -t1/(t2 - t1), div_pos (by linarith) (by linarith),
                div_pos (by linarith) (by linarith), by field_simp; ring, ?_⟩
              ext i
              simp only [hu, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              field_simp; ring
            have side : ∀ x1 ∈ B, ∀ x2 ∈ B, ∀ z ∈ segment ℝ u v, z ∈ openSegment ℝ x1 x2 →
                x1 ∈ segment ℝ u v := by
              intro x1 hx1 x2 hx2 z hz hzx
              obtain ⟨τ, hτ1, hτ2, rfl⟩ := seg2 z hz
              obtain ⟨p1, p2, hp1, hp2, h12, hzeq⟩ := hzx
              set δ := x1 - (s + τ • e) with hδ
              have hz1 : (s + τ • e) + (1:ℝ) • δ ∈ B := by rw [one_smul, hδ, add_sub_cancel]; exact hx1
              have hz2 : (s + τ • e) + (-(p1/p2)) • δ ∈ B := by
                convert hx2 using 1
                ext i
                have := congrFun hzeq i
                simp only [hδ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
                field_simp
                rw [show p1 = 1 - p2 by linarith] at this ⊢
                linarith
              have hzint := interval _ δ 1 (p1/p2) (by positivity) hz1 hz2
              have hθ : ∃ (θ : ℝ) (w : Fin (d+1) → ℝ), 0 < θ ∧ θ ≤ 1 ∧ w ∈ B ∧ s = θ • (s + τ • e) + (1 - θ) • w := by
                rcases le_or_gt 0 τ with hτ | hτ
                · have hne' : τ - t1 ≠ 0 := (by linarith : (0:ℝ) < τ - t1).ne'
                  refine ⟨-t1/(τ - t1), u, div_pos (by linarith) (by linarith),
                    (div_le_one (by linarith)).mpr (by linarith), huB, ?_⟩
                  ext i
                  simp only [hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                  field_simp; ring
                · have hne' : t2 - τ ≠ 0 := (by linarith : (0:ℝ) < t2 - τ).ne'
                  refine ⟨t2/(t2 - τ), v, div_pos (by linarith) (by linarith),
                    (div_le_one (by linarith)).mpr (by linarith), hvB, ?_⟩
                  ext i
                  simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                  field_simp; ring
              obtain ⟨θ, w, hθ0, hθ1, hw, hsθ⟩ := hθ
              have hDδ : Dm δ := by
                refine ⟨θ * min 1 (p1/p2), by positivity, fun t ht => ?_⟩
                have hm := min_le_left 1 (p1/p2)
                have hm2 := min_le_right 1 (p1/p2)
                rw [abs_le] at ht
                have hk := hzint (t/θ) (by rw [le_div_iff₀ hθ0]; nlinarith)
                  (by rw [div_le_iff₀ hθ0]; nlinarith)
                have := hconv hk hw (a := θ) (b := 1 - θ) hθ0.le (by linarith) (by ring)
                convert this using 1
                conv_lhs => rw [hsθ]
                ext i
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                field_simp; ring
              have hpar := par δ hDδ
              have hx1e : x1 = s + (τ + δ 0 / e 0) • e := by
                have : x1 = (s + τ • e) + δ := by rw [hδ]; abel
                rw [this]
                conv_lhs => rw [hpar]
                rw [add_smul, add_assoc]
              have hmem : τ + δ 0 / e 0 ∈ T := by show _ ∈ B; rw [← hx1e]; exact hx1
              rw [hx1e]
              exact seg1 _ (hT1 _ hmem) (hT2 _ hmem)
            refine ⟨u, v, ⟨huv, hconv.segment_subset huB hvB, ?_⟩, hsuv⟩
            intro x1 hx1 x2 hx2 z hz hzx
            exact side x1 hx1 x2 hx2 z hz hzx
          have hfr : ∀ j, ∀ m : ℤ, (m : ℝ) ≠ f j := by
            intro j m h
            obtain ⟨h1, h2⟩ := hf j
            rw [← h] at h1 h2
            have : α j < m := by exact_mod_cast h1
            have : m < α j + 1 := by exact_mod_cast h2
            omega
          have hext_ne : ∀ p ∈ Set.extremePoints ℝ B, ∀ j, p 0 ≠ f j := by
            intro p hp j h
            obtain ⟨m, hm⟩ := hN p hp
            exact hfr j m (hm.symm.trans h)
          have hSdef : ∀ s, s ∈ S ↔ ∃ j, s ∈ Set.extremePoints ℝ (slice B (f j)) := fun s => Set.mem_iUnion
          have P1 : ∀ s ∈ S, ∃ u v, Hirsch.Adj B u v ∧ s ∈ openSegment ℝ u v := by
            intro s hs
            obtain ⟨j, hj⟩ := (hSdef s).1 hs
            exact key (f j) (fun p hp => hext_ne p hp j) s hj
          have hextS : Set.extremePoints ℝ (convexHull ℝ S) ⊆ S := extremePoints_convexHull_subset
          have hAdjsymm : ∀ u v, Hirsch.Adj B u v → Hirsch.Adj B v u := by
            intro u v huv
            refine ⟨huv.1.symm, ?_⟩
            rw [segment_symm]; exact huv.2
          have endpt : ∀ u v, Hirsch.Adj B u v → u ∈ Set.extremePoints ℝ B := by
            intro u v huv
            apply huv.2.extremePoints_subset_extremePoints
            rw [mem_extremePoints_iff_left]
            refine ⟨left_mem_segment ℝ u v, fun x1 hx1 x2 hx2 hu => ?_⟩
            rw [segment_eq_image'] at hx1 hx2
            obtain ⟨t1, ⟨ht10, ht11⟩, rfl⟩ := hx1
            obtain ⟨t2, ⟨ht20, ht21⟩, rfl⟩ := hx2
            obtain ⟨a, b, ha, hb, hab, hu⟩ := hu
            have hw : (a*t1+b*t2) • (v - u) = 0 := by
              linear_combination (norm := module) hu - hab • u
            rcases smul_eq_zero.mp hw with h | h
            · have h' : a * t1 = 0 := by nlinarith [mul_nonneg ha.le ht10, mul_nonneg hb.le ht20]
              have : t1 = 0 := (mul_eq_zero.mp h').resolve_left ha.ne'
              simp [this]
            · exact absurd (sub_eq_zero.mp h) (Ne.symm huv.1)
          have seginj : ∀ u v : Fin (d+1) → ℝ, u 0 ≠ v 0 → ∀ x ∈ segment ℝ u v, ∀ y ∈ segment ℝ u v,
              x 0 = y 0 → x = y := by
            intro u v huv x hx y hy hxy
            rw [segment_eq_image'] at hx hy
            obtain ⟨t, -, rfl⟩ := hx
            obtain ⟨t', -, rfl⟩ := hy
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hxy
            have h0 : (t - t') * (v 0 - u 0) = 0 := by linear_combination hxy
            have : t = t' := by
              rcases mul_eq_zero.mp h0 with h | h
              · linarith
              · exact absurd (by linarith : u 0 = v 0) huv
            rw [this]
          have hS0 : ∀ q ∈ S, ∃ j, q 0 = f j ∧ q ∈ B := by
            intro q hq
            obtain ⟨j, hj⟩ := (hSdef q).1 hq
            exact ⟨j, hj.1.2, hj.1.1⟩
          refine ⟨P1, fun s hs => P1 s (hextS hs), fun u v huv => ⟨?_, ?_⟩⟩
          · rintro ⟨s, hsS, hso⟩
            classical
            have hu := endpt u v huv
            have hv := endpt v u (hAdjsymm u v huv)
            have hSu : ∀ q ∈ S, q ≠ u := by
              intro q hq h
              obtain ⟨j, hj, -⟩ := hS0 q hq
              rw [h] at hj
              exact hext_ne u hu j hj
            have hSv : ∀ q ∈ S, q ≠ v := by
              intro q hq h
              obtain ⟨j, hj, -⟩ := hS0 q hq
              rw [h] at hj
              exact hext_ne v hv j hj
            have huv0 : u 0 ≠ v 0 := by
              intro h
              obtain ⟨j, hj, -⟩ := hS0 s hsS
              obtain ⟨a, b, ha, hb, hab, hs⟩ := hso
              have h1 := congrFun hs 0
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
              rw [← h] at h1
              have : s 0 = u 0 := by linear_combination -h1 + u 0 * hab
              exact hext_ne u hu j (this.symm.trans hj)
            let ψ : (Fin (d+1) → ℝ) → ℝ := fun p => (p 0 - u 0) * (v 0 - u 0)
            let J := Finset.univ.filter (fun j => ∃ p ∈ S, p ∈ openSegment ℝ u v ∧ p 0 = f j)
            have hJne : J.Nonempty := by
              obtain ⟨j, hj, -⟩ := hS0 s hsS
              exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, hsS, hso, hj⟩⟩
            obtain ⟨j0, hj0J, hj0min⟩ := J.exists_min_image (fun j => (f j - u 0) * (v 0 - u 0)) hJne
            obtain ⟨-, s0, hs0S, hs0o, hs00⟩ := Finset.mem_filter.mp hj0J
            have hmin : ∀ q ∈ S, q ∈ segment ℝ u v → ψ s0 ≤ ψ q := by
              intro q hq hqseg
              have hqo : q ∈ openSegment ℝ u v :=
                mem_openSegment_of_ne_left_right (hSu q hq).symm (hSv q hq).symm hqseg
              obtain ⟨j, hj, -⟩ := hS0 q hq
              have := hj0min j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, hqo, hj⟩)
              show (s0 0 - u 0) * (v 0 - u 0) ≤ (q 0 - u 0) * (v 0 - u 0)
              rw [hs00, hj]; exact this
            have hψlin : ∀ (x y : Fin (d+1) → ℝ) (a b : ℝ), a + b = 1 →
                ψ (a • x + b • y) = a * ψ x + b * ψ y := by
              intro x y a b hab
              show ((a • x + b • y) 0 - u 0) * (v 0 - u 0) =
                a * ((x 0 - u 0) * (v 0 - u 0)) + b * ((y 0 - u 0) * (v 0 - u 0))
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rw [show a = 1 - b by linarith]; ring
            let K : Set (Fin (d+1) → ℝ) := {p | p ∈ B ∧ (p ∈ segment ℝ u v → ψ s0 ≤ ψ p)}
            have hKconv : Convex ℝ K := by
              intro x hx y hy a b ha hb hab
              refine ⟨hconv hx.1 hy.1 ha hb hab, fun hseg => ?_⟩
              rcases eq_or_lt_of_le ha with ha0 | ha0
              · have hb1 : b = 1 := by linarith
                have : a • x + b • y = y := by rw [← ha0, hb1]; simp
                rw [this] at hseg ⊢; exact hy.2 hseg
              rcases eq_or_lt_of_le hb with hb0 | hb0
              · have ha1 : a = 1 := by linarith
                have : a • x + b • y = x := by rw [← hb0, ha1]; simp
                rw [this] at hseg ⊢; exact hx.2 hseg
              have hzo : a • x + b • y ∈ openSegment ℝ x y := ⟨a, b, ha0, hb0, hab, rfl⟩
              have hxs : x ∈ segment ℝ u v := huv.2.2 hx.1 hy.1 hseg hzo
              have hys : y ∈ segment ℝ u v :=
                huv.2.2 hy.1 hx.1 hseg (by rw [openSegment_symm]; exact hzo)
              have hxψ := hx.2 hxs
              have hyψ := hy.2 hys
              rw [hψlin x y a b hab]
              calc ψ s0 = a * ψ s0 + b * ψ s0 := by rw [← add_mul, hab, one_mul]
                _ ≤ a * ψ x + b * ψ y :=
                  add_le_add (mul_le_mul_of_nonneg_left hxψ ha) (mul_le_mul_of_nonneg_left hyψ hb)
            have hSK : S ⊆ K := fun q hq => ⟨(hS0 q hq).choose_spec.2, hmin q hq⟩
            have hcK : convexHull ℝ S ⊆ K := convexHull_min hSK hKconv
            refine ⟨s0, ?_, hs0o⟩
            rw [mem_extremePoints_iff_left]
            refine ⟨subset_convexHull ℝ S hs0S, fun x1 hx1 x2 hx2 hx => ?_⟩
            have hK1 := hcK hx1
            have hK2 := hcK hx2
            have hs0seg : s0 ∈ segment ℝ u v := openSegment_subset_segment ℝ u v hs0o
            have hx1s : x1 ∈ segment ℝ u v := huv.2.2 hK1.1 hK2.1 hs0seg hx
            have hx2s : x2 ∈ segment ℝ u v :=
              huv.2.2 hK2.1 hK1.1 hs0seg (by rw [openSegment_symm]; exact hx)
            have h1 := hK1.2 hx1s
            have h2 := hK2.2 hx2s
            obtain ⟨a, b, ha, hb, hab, hxeq⟩ := hx
            have hψeq : ψ s0 = a * ψ x1 + b * ψ x2 := by rw [← hxeq]; exact hψlin x1 x2 a b hab
            have hsum : a * (ψ x1 - ψ s0) + b * (ψ x2 - ψ s0) = 0 := by
              rw [hψeq]; linear_combination (-(a * ψ x1 + b * ψ x2)) * hab
            have k1 := mul_nonneg ha.le (sub_nonneg.mpr h1)
            have k2 := mul_nonneg hb.le (sub_nonneg.mpr h2)
            have k3 : a * (ψ x1 - ψ s0) = 0 := by linarith
            have k4 : ψ x1 - ψ s0 = 0 := (mul_eq_zero.mp k3).resolve_left ha.ne'
            have k5 : (x1 0 - u 0) * (v 0 - u 0) = (s0 0 - u 0) * (v 0 - u 0) := by
              have := k4; simp only [ψ] at this; linarith
            have k6 : x1 0 = s0 0 := by
              have := mul_right_cancel₀ (sub_ne_zero.mpr huv0.symm) k5
              linarith
            exact seginj u v huv0 x1 hx1s s0 hs0seg k6
          · rintro ⟨s, hs, hso⟩
            exact ⟨s, hextS hs, hso⟩
