-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.Supplement.theorem_4_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:53.683468+00:00
-- url     : https://prove2.me/submissions/4cc0c010-ca80-4ed4-a85a-cccbaaf41c49

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

open BinaryExtForm
open BinaryExtForm.HypercubeRank
open BinaryExtForm.HypercubeRank.Supplement

open BinaryExtForm.HypercubeRank
theorem solution {n p d k ℓ : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ)) (hP : IsPolytope P)
    (hPk : ∀ x ∈ P, ∀ i : Fin p, 0 ≤ xc hpn x i ∧ xc hpn x i ≤ k)
    (B : Fin p → Set (Fin (d + 1) → ℝ)) (hB : ∀ i, IsBinarization d k (B i))
    (hN : ∀ i, IsNatural (B i)) (α : Fin ℓ → ℤ) (i : Fin p)
    (zbar : Fin ℓ → Pt n p d) (hz : ∀ j, zbar j ∈ Set.extremePoints ℝ (BEF hpn P B))
    (hzi : ∀ j, (α j : ℝ) < xc hpn (zbar j).1 i ∧ xc hpn (zbar j).1 i < α j + 1) :
    propRank hpn P B i α =
      lpr (convexHull ℝ (⋃ j, slice (B i) (xc hpn (zbar j).1 i))) (yCoords d) := by
        classical
        -- generic: extreme points of one split
        have hA : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (S : Set E), Convex ℝ S →
            ∀ (f : E →ₗ[ℝ] ℝ), (∀ z ∈ S, 0 ≤ f z ∧ f z ≤ 1) →
            Set.extremePoints ℝ (convexHull ℝ (S ∩ {z | f z = 0 ∨ f z = 1})) =
              Set.extremePoints ℝ S ∩ {z | f z = 0 ∨ f z = 1} := by
          intro E _ _ S hS f hf
          apply Set.Subset.antisymm
          · intro v hv
            have hvH : v ∈ S ∩ {z | f z = 0 ∨ f z = 1} := extremePoints_convexHull_subset hv
            refine ⟨?_, hvH.2⟩
            rw [mem_extremePoints] at hv ⊢
            refine ⟨hvH.1, fun a ha b hb hab => ?_⟩
            obtain ⟨s, t, hs, ht, hst, rfl⟩ := hab
            have hfa := hf a ha
            have hfb := hf b hb
            have key : f (s • a + t • b) = s * f a + t * f b := by simp
            have haH : f a = 0 ∨ f a = 1 := by
              rcases hvH.2 with h | h <;> rw [key] at h
              · left; nlinarith
              · right; nlinarith
            have hbH : f b = 0 ∨ f b = 1 := by
              rcases hvH.2 with h | h <;> rw [key] at h
              · left; nlinarith
              · right; nlinarith
            exact hv.2 a (subset_convexHull ℝ _ ⟨ha, haH⟩) b (subset_convexHull ℝ _ ⟨hb, hbH⟩)
              ⟨s, t, hs, ht, hst, rfl⟩
          · rintro v ⟨hv, hvH⟩
            exact inter_extremePoints_subset_extremePoints_of_subset
              (convexHull_min Set.inter_subset_left hS)
              ⟨subset_convexHull ℝ _ ⟨hv.1, hvH⟩, hv⟩
        -- the coordinate functional y_{i,h}
        let fy : Fin d → (Pt n p d →ₗ[ℝ] ℝ) := fun h =>
          (LinearMap.proj h).comp ((LinearMap.proj i).comp (LinearMap.snd ℝ (Fin n → ℝ) (Fin p → Fin d → ℝ)))
        have hfy : ∀ h z, fy h z = z.2 i h := fun h z => rfl
        -- BEF is convex
        have hblock : ∀ (a b : Pt n p d) (s t : ℝ) (i' : Fin p),
            block hpn (s • a + t • b) i' = s • block hpn a i' + t • block hpn b i' := by
          intro a b s t i'
          funext m
          refine Fin.cases ?_ (fun m => ?_) m <;> simp [block, xc]
        have hPc : Convex ℝ P := by
          obtain ⟨S, rfl⟩ := hP; exact convex_convexHull ℝ _
        have hBc : ∀ i', Convex ℝ (B i') := by
          intro i'; obtain ⟨S, hS⟩ := (hB i').1; rw [hS]; exact convex_convexHull ℝ _
        have hQc : Convex ℝ (BEF hpn P B) := by
          intro a ha b hb s t hs ht hst
          refine ⟨hPc ha.1 hb.1 hs ht hst, fun i' j' => ?_, fun i' => ?_⟩
          · have h1 := ha.2.1 i' j'
            have h2 := hb.2.1 i' j'
            simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            constructor <;> nlinarith
          · rw [hblock]; exact hBc i' (ha.2.2 i') (hb.2.2 i') hs ht hst
        -- iterated splits
        have hiter : ∀ (l : List (Fin d)) (S : Set (Pt n p d)), Convex ℝ S → S ⊆ BEF hpn P B →
            Convex ℝ (iterYSplit S i l) ∧ iterYSplit S i l ⊆ BEF hpn P B ∧
            Set.extremePoints ℝ (iterYSplit S i l) =
              Set.extremePoints ℝ S ∩ {z | ∀ h ∈ l, z.2 i h = 0 ∨ z.2 i h = 1} := by
          intro l
          induction l with
          | nil => intro S hS hSQ; simp [iterYSplit, hS, hSQ]
          | cons h l ih =>
            intro S hS hSQ
            have hsub : ySplit S i h ⊆ S := convexHull_min Set.inter_subset_left hS
            have hc : Convex ℝ (ySplit S i h) := convex_convexHull ℝ _
            obtain ⟨h1, h2, h3⟩ := ih (ySplit S i h) hc (hsub.trans hSQ)
            refine ⟨h1, h2, ?_⟩
            have e : iterYSplit S i (h :: l) = iterYSplit (ySplit S i h) i l := rfl
            rw [e, h3]
            have := hA S hS (fy h) (fun z hz => (hSQ hz).2.1 i h)
            simp only [hfy] at this
            rw [ySplit, this]
            ext z
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_cons]
            constructor
            · rintro ⟨⟨a, b⟩, c⟩
              exact ⟨a, fun h' hh => hh.elim (fun e => e ▸ b) (c h')⟩
            · rintro ⟨a, b⟩
              exact ⟨⟨a, b h (Or.inl rfl)⟩, fun h' hh => b h' (Or.inr hh)⟩
        have hQrank : propRank hpn P B i α = sInf {t : ℕ | ∃ l : List (Fin d), l.length = t ∧
            ∀ z ∈ Set.extremePoints ℝ (BEF hpn P B), (∀ h ∈ l, z.2 i h = 0 ∨ z.2 i h = 1) →
              ∀ j, xc hpn z.1 i ≤ α j ∨ (α j : ℝ) + 1 ≤ xc hpn z.1 i} := by
          unfold propRank SatisfiesP
          congr 1
          ext t
          simp only [Set.mem_setOf_eq]
          refine exists_congr fun l => and_congr_right fun _ => ?_
          rw [(hiter l _ hQc subset_rfl).2.2]
          constructor
          · intro H z hz hl; exact H z ⟨hz, hl⟩
          · rintro H z ⟨hz, hl⟩; exact H z hz hl
        rw [hQrank]
        have hF : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (U : Set E) (f : E →ₗ[ℝ] ℝ) (c : ℝ),
            (∀ u ∈ U, f u ≤ c) → ∀ w ∈ convexHull ℝ U, f w = c →
              w ∈ convexHull ℝ (U ∩ {u | f u = c}) := by
          intro E _ _ U f c hU
          have hle : ∀ w ∈ convexHull ℝ U, f w ≤ c := fun w hw =>
            convexHull_min (fun u hu => hU u hu) (convex_halfSpace_le f.isLinear c) hw
          have hK : convexHull ℝ U ⊆ {x | x ∈ convexHull ℝ U ∧
              (f x = c → x ∈ convexHull ℝ (U ∩ {u | f u = c}))} := by
            refine convexHull_min (fun u hu => ⟨subset_convexHull ℝ U hu,
              fun h => subset_convexHull ℝ _ ⟨hu, h⟩⟩) ?_
            intro x hx y hy s t hs ht hst
            refine ⟨convex_convexHull ℝ U hx.1 hy.1 hs ht hst, fun h => ?_⟩
            have fx := hle x hx.1
            have fy := hle y hy.1
            have key : f (s • x + t • y) = s * f x + t * f y := by simp
            rw [key] at h
            rcases hs.eq_or_lt with hs0 | hs0
            · subst hs0
              have : t = 1 := by linarith
              subst this
              simp only [zero_smul, one_smul, zero_add] at h ⊢
              exact hy.2 (by linarith)
            rcases ht.eq_or_lt with ht0 | ht0
            · subst ht0
              have : s = 1 := by linarith
              subst this
              simp only [zero_smul, one_smul, add_zero] at h ⊢
              exact hx.2 (by linarith)
            have hc : c = s*c + t*c := by rw [← add_mul, hst, one_mul]
            have e1 : f x = c := by
              by_contra hne
              have hlt := lt_of_le_of_ne fx hne
              linarith [mul_lt_mul_of_pos_left hlt hs0, mul_le_mul_of_nonneg_left fy ht]
            have e2 : f y = c := by
              by_contra hne
              have hlt := lt_of_le_of_ne fy hne
              linarith [mul_lt_mul_of_pos_left hlt ht0, mul_le_mul_of_nonneg_left fx hs]
            exact convex_convexHull ℝ _ (hx.2 e1) (hy.2 e2) hs ht hst
          exact fun w hw h => (hK hw).2 h
        have hFiter : ∀ (l' : List (Fin (d+1))) (U : Set (Fin (d+1) → ℝ)),
            (∀ u ∈ U, ∀ h ∈ l', 0 ≤ u h ∧ u h ≤ 1) → ∀ w ∈ convexHull ℝ U,
            (∀ h ∈ l', w h = 0 ∨ w h = 1) →
              w ∈ convexHull ℝ (U ∩ {u | ∀ h ∈ l', u h = w h}) := by
          intro l'
          induction l' with
          | nil => intro U _ w hw _; simpa using hw
          | cons h l ih =>
            intro U hU w hw hb
            have h1 : w ∈ convexHull ℝ (U ∩ {u | u h = w h}) := by
              rcases hb h (List.mem_cons_self) with e | e
              · have := hF U (-(LinearMap.proj h : (Fin (d+1) → ℝ) →ₗ[ℝ] ℝ)) 0
                  (fun u hu => by simpa using (hU u hu h List.mem_cons_self).1) w hw (by simp [e])
                convert this using 3
                ext u; simp [e]
              · have := hF U ((LinearMap.proj h : (Fin (d+1) → ℝ) →ₗ[ℝ] ℝ)) 1
                  (fun u hu => by simpa using (hU u hu h List.mem_cons_self).2) w hw (by simp [e])
                convert this using 3
                ext u; simp [e]
            have h2 := ih (U ∩ {u | u h = w h})
              (fun u hu h' hh' => hU u hu.1 h' (List.mem_cons_of_mem _ hh')) w h1
              (fun h' hh' => hb h' (List.mem_cons_of_mem _ hh'))
            refine convexHull_mono ?_ h2
            rintro u ⟨⟨hu, e⟩, hl⟩
            refine ⟨hu, fun h' hh' => ?_⟩
            rcases List.mem_cons.1 hh' with rfl | hh'
            · exact e
            · exact hl h' hh'
        have hpert : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (S : Set E) (z : E), Convex ℝ S →
            (z ∈ Set.extremePoints ℝ S ↔ z ∈ S ∧ ∀ δ, z + δ ∈ S → z - δ ∈ S → δ = 0) := by
          intro E _ _ S z hS
          constructor
          · intro hz
            refine ⟨hz.1, fun δ h1 h2 => ?_⟩
            have := hz.2 h1 h2 ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
            simpa using this
          · rintro ⟨hzS, H⟩
            refine ⟨hzS, fun x₁ h₁ x₂ h₂ hseg => ?_⟩
            obtain ⟨s, t, hs, ht, hst, rfl⟩ := hseg
            set ε := min s t with hε
            have hε0 : 0 < ε := lt_min hs ht
            have hεs : ε ≤ s := min_le_left _ _
            have hεt : ε ≤ t := min_le_right _ _
            have e1 : s • x₁ + t • x₂ + ε • (x₁ - x₂) = (s + ε) • x₁ + (t - ε) • x₂ := by module
            have e2 : s • x₁ + t • x₂ - ε • (x₁ - x₂) = (s - ε) • x₁ + (t + ε) • x₂ := by module
            have hd := H (ε • (x₁ - x₂))
              (by rw [e1]; exact hS h₁ h₂ (by linarith) (by linarith) (by linarith))
              (by rw [e2]; exact hS h₁ h₂ (by linarith) (by linarith) (by linarith))
            rw [smul_eq_zero, sub_eq_zero] at hd
            rcases hd with hd | hd
            · exact absurd hd hε0.ne'
            subst hd
            rw [← add_smul, hst, one_smul]
        have hdec : ∀ (w : Fin (d+1) → ℝ), w ∈ B i → ∀ a : ℤ, (a:ℝ) < w 0 → w 0 < a + 1 →
            ∃ pm ∈ B i, ∃ pp ∈ B i, pm 0 ≤ a ∧ (a:ℝ) + 1 ≤ pp 0 ∧
              ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ s • pm + t • pp = w := by
          intro w hw a ha1 ha2
          obtain ⟨F, hF⟩ := (hB i).1
          have hcpt : IsCompact (B i) := by rw [hF]; exact F.finite_toSet.isCompact_convexHull ℝ
          have hconv : Convex ℝ (B i) := hBc i
          have hext_sub : Set.extremePoints ℝ (B i) ⊆ F := by rw [hF]; exact extremePoints_convexHull_subset
          have hfin : (Set.extremePoints ℝ (B i)).Finite := F.finite_toSet.subset hext_sub
          have hKM : convexHull ℝ (Set.extremePoints ℝ (B i)) = B i := by
            have := closure_convexHull_extremePoints hcpt hconv
            rwa [(hfin.isCompact_convexHull ℝ).isClosed.closure_eq] at this
          have hunion : Set.extremePoints ℝ (B i) =
              (Set.extremePoints ℝ (B i) ∩ {p | p 0 ≤ a}) ∪
                (Set.extremePoints ℝ (B i) ∩ {p | (a:ℝ) + 1 ≤ p 0}) := by
            ext q
            constructor
            · intro hq
              obtain ⟨m, hm⟩ := hN i q hq
              by_cases hma : m ≤ a
              · left; refine ⟨hq, ?_⟩; show q 0 ≤ a; rw [hm]; exact_mod_cast hma
              · right; refine ⟨hq, ?_⟩; show (a:ℝ) + 1 ≤ q 0; rw [hm]
                have : a + 1 ≤ m := by omega
                exact_mod_cast this
            · rintro (h | h) <;> exact h.1
          have hc1 : Convex ℝ {q : Fin (d+1) → ℝ | q 0 ≤ a} :=
            convex_halfSpace_le (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d+1) => ℝ) 0).isLinear (a:ℝ)
          have hc2 : Convex ℝ {q : Fin (d+1) → ℝ | (a:ℝ) + 1 ≤ q 0} :=
            convex_halfSpace_ge (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d+1) => ℝ) 0).isLinear _
          have hm_sub : convexHull ℝ (Set.extremePoints ℝ (B i) ∩ {p | p 0 ≤ a}) ⊆ B i ∩ {p | p 0 ≤ a} :=
            convexHull_min (fun q hq => ⟨hKM ▸ subset_convexHull ℝ _ hq.1, hq.2⟩) (hconv.inter hc1)
          have hp_sub : convexHull ℝ (Set.extremePoints ℝ (B i) ∩ {p | (a:ℝ) + 1 ≤ p 0}) ⊆
              B i ∩ {p | (a:ℝ) + 1 ≤ p 0} :=
            convexHull_min (fun q hq => ⟨hKM ▸ subset_convexHull ℝ _ hq.1, hq.2⟩) (hconv.inter hc2)
          have hw' : w ∈ convexHull ℝ ((Set.extremePoints ℝ (B i) ∩ {p | p 0 ≤ a}) ∪
                (Set.extremePoints ℝ (B i) ∩ {p | (a:ℝ) + 1 ≤ p 0})) := by
            rw [← hunion, hKM]; exact hw
          have hne1 : (Set.extremePoints ℝ (B i) ∩ {p | p 0 ≤ a}).Nonempty := by
            by_contra hc
            rw [Set.not_nonempty_iff_eq_empty] at hc
            rw [hc, Set.empty_union] at hw'
            have := (hp_sub hw').2
            simp only [Set.mem_setOf_eq] at this
            linarith
          have hne2 : (Set.extremePoints ℝ (B i) ∩ {p | (a:ℝ) + 1 ≤ p 0}).Nonempty := by
            by_contra hc
            rw [Set.not_nonempty_iff_eq_empty] at hc
            rw [hc, Set.union_empty] at hw'
            have := (hm_sub hw').2
            simp only [Set.mem_setOf_eq] at this
            linarith
          rw [convexHull_union hne1 hne2, mem_convexJoin] at hw'
          obtain ⟨pm, hpm, pp, hpp, s, t, hs, ht, hst, e⟩ := hw'
          exact ⟨pm, (hm_sub hpm).1, pp, (hp_sub hpp).1, (hm_sub hpm).2, (hp_sub hpp).2, s, t, hs, ht, hst, e⟩
        have hhelp : ∀ s t x y : ℝ, 0 < s → 0 < t → s + t = 1 → 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
            (s*x+t*y = 0 ∨ s*x+t*y = 1) → x = s*x+t*y ∧ y = s*x+t*y := by
          intro s t x y hs ht hst hx0 hx1 hy0 hy1 h
          rcases h with h | h
          · have h1 : x = 0 := by nlinarith [mul_nonneg hs.le hx0, mul_nonneg ht.le hy0]
            have h2 : y = 0 := by nlinarith [mul_nonneg hs.le hx0, mul_nonneg ht.le hy0]
            rw [h]; exact ⟨h1, h2⟩
          · have h1 : x = 1 := by nlinarith [mul_nonneg hs.le (sub_nonneg.2 hx1), mul_nonneg ht.le (sub_nonneg.2 hy1)]
            have h2 : y = 1 := by nlinarith [mul_nonneg hs.le (sub_nonneg.2 hx1), mul_nonneg ht.le (sub_nonneg.2 hy1)]
            rw [h]; exact ⟨h1, h2⟩
        have hBy : ∀ q ∈ B i, ∀ h : Fin d, 0 ≤ q h.succ ∧ q h.succ ≤ 1 := fun q hq h => (hB i).2.2.1 q hq h
        have hbinZ : ∀ q ∈ B i, (∀ h : Fin d, q h.succ = 0 ∨ q h.succ = 1) → ∃ m : ℕ, m ≤ k ∧ q 0 = m := by
          intro q hq hb
          have : q 0 ∈ (fun p => p 0) '' {p | p ∈ B i ∧ IsBinaryY p} := ⟨q, ⟨hq, hb⟩, rfl⟩
          rw [(hB i).2.2.2] at this
          exact this
        have hfrac : ∀ j (m : ℕ), xc hpn (zbar j).1 i ≠ m := by
          intro j m hm
          have h1 := (hzi j).1
          have h2 := (hzi j).2
          rw [hm] at h1 h2
          have h1' : α j < (m : ℤ) := by exact_mod_cast h1
          have h2' : (m : ℤ) < α j + 1 := by exact_mod_cast h2
          omega
        have hYsucc : ∀ x ∈ yCoords d, ∃ h : Fin d, h.succ = x := by
          intro x hx; simp only [yCoords, Finset.mem_image] at hx
          obtain ⟨h, _, e⟩ := hx; exact ⟨h, e⟩
        have hsuccY : ∀ h : Fin d, h.succ ∈ yCoords d := fun h =>
          Finset.mem_image_of_mem _ (Finset.mem_univ h)
        -- iterated splits for subsets of B i
        have hiterC : ∀ (l' : List (Fin (d+1))) (S : Set (Fin (d+1) → ℝ)), (∀ x ∈ l', x ∈ yCoords d) →
            Convex ℝ S → S ⊆ B i →
            Set.extremePoints ℝ (Disjunctive.HigherDim.IteratedSplit S l') ⊆ Set.extremePoints ℝ S ∧
            Disjunctive.HigherDim.IteratedSplit S l' ⊆
              convexHull ℝ (S ∩ {u | ∀ h' ∈ l', u h' = 0 ∨ u h' = 1}) := by
          intro l'
          induction l' with
          | nil =>
            intro S _ hS _
            simp only [Disjunctive.HigherDim.IteratedSplit, List.foldl_nil, List.not_mem_nil,
              false_imp_iff, imp_true_iff, Set.setOf_true, Set.inter_univ, hS.convexHull_eq]
            exact ⟨subset_rfl, subset_rfl⟩
          | cons h l ih =>
            intro S hY hS hSB
            have e : Disjunctive.HigherDim.IteratedSplit S (h :: l) =
                Disjunctive.HigherDim.IteratedSplit (convexHull ℝ (S ∩ {u | u h = 0 ∨ u h = 1})) l := rfl
            obtain ⟨h0, rfl⟩ := hYsucc h (hY h List.mem_cons_self)
            have hsub : convexHull ℝ (S ∩ {u | u h0.succ = 0 ∨ u h0.succ = 1}) ⊆ S :=
              convexHull_min Set.inter_subset_left hS
            obtain ⟨ih1, ih2⟩ := ih _ (fun x hx => hY x (List.mem_cons_of_mem _ hx))
              (convex_convexHull ℝ _) (hsub.trans hSB)
            rw [e]
            refine ⟨ih1.trans ?_, ih2.trans ?_⟩
            · have := hA S hS (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d+1) => ℝ) h0.succ)
                (fun z hz => hBy z (hSB hz) h0)
              intro v hv
              exact (this.le hv).1
            · refine convexHull_min ?_ (convex_convexHull ℝ _)
              rintro w ⟨hw, hwb⟩
              have := hFiter l (S ∩ {u | u h0.succ = 0 ∨ u h0.succ = 1})
                (fun u hu h' hh' => by
                  obtain ⟨h1, rfl⟩ := hYsucc h' (hY h' (List.mem_cons_of_mem _ hh'))
                  exact hBy u (hSB hu.1) h1) w hw hwb
              refine convexHull_mono ?_ this
              rintro u ⟨⟨hu, hub⟩, hl⟩
              refine ⟨hu, fun h' hh' => ?_⟩
              rcases List.mem_cons.1 hh' with rfl | hh'
              · exact hub
              · rw [hl h' hh']; exact hwb h' hh'
        have hcont : ∀ (l' : List (Fin (d+1))) (S : Set (Fin (d+1) → ℝ)),
            S ∩ {u | ∀ h' ∈ l', u h' = 0 ∨ u h' = 1} ⊆ Disjunctive.HigherDim.IteratedSplit S l' := by
          intro l'
          induction l' with
          | nil => intro S; exact Set.inter_subset_left
          | cons h l ih =>
            intro S w ⟨hw, hb⟩
            have e : Disjunctive.HigherDim.IteratedSplit S (h :: l) =
                Disjunctive.HigherDim.IteratedSplit (convexHull ℝ (S ∩ {u | u h = 0 ∨ u h = 1})) l := rfl
            rw [e]
            exact ih _ ⟨subset_convexHull ℝ _ ⟨hw, hb h List.mem_cons_self⟩,
              fun h' hh' => hb h' (List.mem_cons_of_mem _ hh')⟩
        -- the set C
        have hSB : ∀ j, slice (B i) (xc hpn (zbar j).1 i) ⊆ B i := fun j q hq => hq.1
        have hUB : (⋃ j, slice (B i) (xc hpn (zbar j).1 i)) ⊆ B i := Set.iUnion_subset hSB
        have hCB : convexHull ℝ (⋃ j, slice (B i) (xc hpn (zbar j).1 i)) ⊆ B i :=
          convexHull_min hUB (hBc i)
        have hLN : ∀ l' : List (Fin (d+1)), (∀ x ∈ l', x ∈ yCoords d) →
            (Disjunctive.HigherDim.IteratedSplit (convexHull ℝ (⋃ j, slice (B i) (xc hpn (zbar j).1 i))) l' =
              intHull (convexHull ℝ (⋃ j, slice (B i) (xc hpn (zbar j).1 i))) (yCoords d) ↔
             ∀ j, ∀ w ∈ B i, w 0 = xc hpn (zbar j).1 i → ¬ ∀ h' ∈ l', w h' = 0 ∨ w h' = 1) := by
          intro l' hY
          set U := ⋃ j, slice (B i) (xc hpn (zbar j).1 i) with hU
          set C := convexHull ℝ U with hC
          obtain ⟨hI1, hI2⟩ := hiterC l' C hY (convex_convexHull ℝ _) hCB
          have hbinall : ∀ q ∈ C ∩ ⋂ x ∈ yCoords d, Disjunctive.HigherDim.ZeroOneSet x,
              ∀ h : Fin d, q h.succ = 0 ∨ q h.succ = 1 := fun q hq h =>
            Set.mem_iInter₂.1 hq.2 h.succ (hsuccY h)
          constructor
          · intro hL j w hw hw0 hwb
            have hwI : w ∈ intHull C (yCoords d) := by
              rw [← hL]; exact hcont l' C ⟨subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨j, hw, hw0⟩), hwb⟩
            have hfin : (C ∩ ⋂ x ∈ yCoords d, Disjunctive.HigherDim.ZeroOneSet x).Finite := by
              let A : Finset ℝ := (Finset.range (k+1)).image (fun m : ℕ => (m:ℝ)) ∪ {0, 1}
              refine (Set.Finite.pi (t := fun _ : Fin (d+1) => (A : Set ℝ)) (fun _ => A.finite_toSet)).subset ?_
              intro q hq
              simp only [Set.mem_pi, Set.mem_univ, true_imp_iff]
              intro m
              refine Fin.cases ?_ (fun h => ?_) m
              · obtain ⟨m0, hm0, e⟩ := hbinZ q (hCB hq.1) (hbinall q hq)
                simp only [A, Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
                  Set.mem_image, Set.mem_Iio]
                left; exact ⟨m0, by omega, e.symm⟩
              · simp only [A, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton, Set.mem_union,
                  Set.mem_insert_iff, Set.mem_singleton_iff]
                right; exact hbinall q hq h
            have hcpt : IsCompact (intHull C (yCoords d)) := hfin.isCompact_convexHull ℝ
            obtain ⟨v, hv⟩ := hcpt.extremePoints_nonempty ⟨w, hwI⟩
            have hv1 : v ∈ C ∩ ⋂ x ∈ yCoords d, Disjunctive.HigherDim.ZeroOneSet x :=
              extremePoints_convexHull_subset hv
            have hv2 : v ∈ U := by
              rw [← hL] at hv
              exact extremePoints_convexHull_subset (hI1 hv)
            obtain ⟨j', hj'⟩ := Set.mem_iUnion.1 hv2
            obtain ⟨m0, _, e⟩ := hbinZ v (hCB hv1.1) (hbinall v hv1)
            exact hfrac j' m0 (hj'.2.symm.trans e)
          · intro hNl
            have hempty : C ∩ {u | ∀ h' ∈ l', u h' = 0 ∨ u h' = 1} = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro w ⟨hw, hwb⟩
              have := hFiter l' U (fun u hu h' hh' => by
                  obtain ⟨h1, rfl⟩ := hYsucc h' (hY h' hh')
                  exact hBy u (hUB hu) h1) w hw hwb
              obtain ⟨u, ⟨hu, hul⟩⟩ := (convexHull_nonempty_iff.1 ⟨w, this⟩)
              obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
              exact hNl j u hj.1 hj.2 (fun h' hh' => by rw [hul h' hh']; exact hwb h' hh')
            have e1 : Disjunctive.HigherDim.IteratedSplit C l' = ∅ := by
              have := hI2; rw [hempty, convexHull_empty] at this
              exact Set.eq_empty_of_subset_empty this
            have e2 : intHull C (yCoords d) = ∅ := by
              unfold intHull
              rw [convexHull_eq_empty]
              rw [Set.eq_empty_iff_forall_notMem]
              intro q hq
              have : q ∈ C ∩ {u | ∀ h' ∈ l', u h' = 0 ∨ u h' = 1} := ⟨hq.1, fun h' hh' => by
                obtain ⟨h1, rfl⟩ := hYsucc h' (hY h' hh')
                exact hbinall q hq h1⟩
              rw [hempty] at this; exact this
            rw [e1, e2]
        have hblk0 : ∀ z : Pt n p d, block hpn z i 0 = xc hpn z.1 i := fun z => rfl
        have hblks : ∀ (z : Pt n p d) (i' : Fin p) (h : Fin d), block hpn z i' h.succ = z.2 i' h :=
          fun z i' h => rfl
        -- transport along a decomposition
        have htrans : ∀ (w : Fin (d+1) → ℝ), w ∈ B i → ∀ j, (α j : ℝ) < w 0 → w 0 < α j + 1 →
            ∃ pm ∈ B i, ∃ pp ∈ B i, pm 0 < w 0 ∧ w 0 < pp 0 ∧ pm 0 ≤ α j ∧ (α j : ℝ) + 1 ≤ pp 0 ∧
              (∀ h : Fin d, (w h.succ = 0 ∨ w h.succ = 1) → pm h.succ = w h.succ ∧ pp h.succ = w h.succ) ∧
              w = pm + ((w 0 - pm 0) / (pp 0 - pm 0)) • (pp - pm) := by
          intro w hw j h1 h2
          obtain ⟨pm, hpm, pp, hpp, hm, hp, s, t, hs, ht, hst, e⟩ := hdec w hw (α j) h1 h2
          have e0 : w 0 = s * pm 0 + t * pp 0 := by rw [← e]; simp
          have hs0 : 0 < s := by
            rcases hs.eq_or_lt with h | h
            · exfalso; rw [← h] at hst e0
              have ht1 : t = 1 := by linarith
              rw [ht1] at e0; linarith
            · exact h
          have ht0 : 0 < t := by
            rcases ht.eq_or_lt with h | h
            · exfalso; rw [← h] at hst e0
              have ht1 : s = 1 := by linarith
              rw [ht1] at e0; linarith
            · exact h
          refine ⟨pm, hpm, pp, hpp, by nlinarith, by nlinarith, hm, hp, fun h hb => ?_, ?_⟩
          · have eh : w h.succ = s * pm h.succ + t * pp h.succ := by rw [← e]; simp
            have := hhelp s t (pm h.succ) (pp h.succ) hs0 ht0 hst (hBy pm hpm h).1 (hBy pm hpm h).2
              (hBy pp hpp h).1 (hBy pp hpp h).2 (eh ▸ hb)
            rw [eh]; exact this
          · have hne : pp 0 - pm 0 ≠ 0 := by linarith
            have ht' : t = (w 0 - pm 0) / (pp 0 - pm 0) := by
              field_simp; rw [e0]; have : s = 1 - t := by linarith
              subst this; ring
            rw [← ht', ← e]
            have : s = 1 - t := by linarith
            subst this; module
        have hNH : ∀ l : List (Fin d), (∀ j, ∀ w ∈ B i, w 0 = xc hpn (zbar j).1 i →
              ¬ ∀ h ∈ l, w h.succ = 0 ∨ w h.succ = 1) →
            ∀ z ∈ Set.extremePoints ℝ (BEF hpn P B), (∀ h ∈ l, z.2 i h = 0 ∨ z.2 i h = 1) →
              ∀ j, xc hpn z.1 i ≤ α j ∨ (α j : ℝ) + 1 ≤ xc hpn z.1 i := by
          intro l hNl z hz hl j
          by_contra hc
          push_neg at hc
          have hu := hz.1.2.2 i
          obtain ⟨pm, hpm, pp, hpp, hm0, hp0, hm, hp, hbin, -⟩ :=
            htrans (block hpn z i) hu j (by rw [hblk0]; exact hc.1) (by rw [hblk0]; exact hc.2)
          set b := (xc hpn (zbar j).1 i - pm 0) / (pp 0 - pm 0) with hb
          have hne : 0 < pp 0 - pm 0 := by linarith
          have hb0 : 0 ≤ b := div_nonneg (by linarith [(hzi j).1]) hne.le
          have hb1 : b ≤ 1 := (div_le_one hne).2 (by linarith [(hzi j).2])
          have hW : pm + b • (pp - pm) ∈ B i := (hBc i).starConvex hpm |>.add_smul_sub_mem hpp hb0 hb1
          refine hNl j _ hW ?_ ?_
          · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hb]
            field_simp; ring
          · intro h hh
            have := hbin h (by rw [hblks]; exact hl h hh)
            simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, this.1, this.2, sub_self,
              mul_zero, add_zero, hblks]
            exact hl h hh
        have hHN : ∀ l : List (Fin d), (∀ z ∈ Set.extremePoints ℝ (BEF hpn P B),
              (∀ h ∈ l, z.2 i h = 0 ∨ z.2 i h = 1) →
              ∀ j, xc hpn z.1 i ≤ α j ∨ (α j : ℝ) + 1 ≤ xc hpn z.1 i) →
            (∀ j, ∀ w ∈ B i, w 0 = xc hpn (zbar j).1 i → ¬ ∀ h ∈ l, w h.succ = 0 ∨ w h.succ = 1) := by
          intro l hH j w hw hw0 hwb
          obtain ⟨F, hF⟩ := (hB i).1
          have hBcpt : IsCompact (B i) := by rw [hF]; exact F.finite_toSet.isCompact_convexHull ℝ
          have hSconv : Convex ℝ (B i ∩ {q : Fin (d+1) → ℝ | q 0 = xc hpn (zbar j).1 i}) :=
            (hBc i).inter (convex_hyperplane (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d+1) => ℝ) 0).isLinear _)
          have hTc : IsCompact ((B i ∩ {q : Fin (d+1) → ℝ | q 0 = xc hpn (zbar j).1 i}) ∩
              {q | ∀ h ∈ l, q h.succ = w h.succ}) := by
            refine (hBcpt.inter_right (isClosed_eq (continuous_apply 0) continuous_const)).inter_right ?_
            simp only [Set.setOf_forall]
            exact isClosed_iInter fun h => isClosed_iInter fun _ =>
              isClosed_eq (continuous_apply _) continuous_const
          obtain ⟨v, hvT⟩ := hTc.extremePoints_nonempty ⟨w, ⟨hw, hw0⟩, fun h _ => rfl⟩
          have hText : IsExtreme ℝ (B i ∩ {q : Fin (d+1) → ℝ | q 0 = xc hpn (zbar j).1 i})
              ((B i ∩ {q : Fin (d+1) → ℝ | q 0 = xc hpn (zbar j).1 i}) ∩
              {q | ∀ h ∈ l, q h.succ = w h.succ}) := by
            refine ⟨Set.inter_subset_left, fun x₁ h₁ x₂ h₂ x hx hseg => ?_⟩
            obtain ⟨s, t, hs, ht, hst, rfl⟩ := hseg
            have key : ∀ h ∈ l, x₁ h.succ = w h.succ ∧ x₂ h.succ = w h.succ := by
              intro h hh
              have e1 := hx.2 h hh
              have e2 : (s • x₁ + t • x₂) h.succ = s * x₁ h.succ + t * x₂ h.succ := by simp
              have := hhelp s t (x₁ h.succ) (x₂ h.succ) hs ht hst (hBy _ h₁.1 h).1 (hBy _ h₁.1 h).2
                (hBy _ h₂.1 h).1 (hBy _ h₂.1 h).2 (by rw [← e2, e1]; exact hwb h hh)
              rw [← e2, e1] at this; exact this
            exact ⟨h₁, fun h hh => (key h hh).1⟩
          have hvS := hText.extremePoints_subset_extremePoints hvT
          have hv0 : v 0 = xc hpn (zbar j).1 i := hvS.1.2
          set zb := zbar j with hzb
          set z : Pt n p d := (zb.1, Function.update zb.2 i (fun h => v h.succ)) with hzdef
          have hzQ : z ∈ BEF hpn P B := by
            refine ⟨(hz j).1.1, fun i' h => ?_, fun i' => ?_⟩
            · by_cases hi : i' = i
              · subst hi; simp only [z, Function.update_self]; exact hBy v hvS.1.1 h
              · simp only [z, Function.update_of_ne hi]; exact (hz j).1.2.1 i' h
            · by_cases hi : i' = i
              · subst hi
                have : block hpn z i' = v := by
                  funext m; refine Fin.cases ?_ (fun h => ?_) m
                  · simp [block, z, hv0, xc, hzb]
                  · simp [block, z]
                rw [this]; exact hvS.1.1
              · have : block hpn z i' = block hpn zb i' := by
                  funext m; refine Fin.cases ?_ (fun h => ?_) m
                  · simp [block, z]
                  · simp [block, z, Function.update_of_ne hi]
                rw [this]; exact (hz j).1.2.2 i'
          have hzext : z ∈ Set.extremePoints ℝ (BEF hpn P B) := by
            refine (hpert _ z hQc).2 ⟨hzQ, fun δ h1 h2 => ?_⟩
            have hwb0 : (α j : ℝ) < block hpn zb i 0 := (hzi j).1
            have hwb1 : block hpn zb i 0 < α j + 1 := (hzi j).2
            obtain ⟨pm, hpm, pp, hpp, hm0, hp0, -, -, -, hrep⟩ :=
              htrans (block hpn zb i) ((hz j).1.2.2 i) j hwb0 hwb1
            set wb := block hpn zb i with hwbdef
            set Δ := pp 0 - pm 0 with hΔ
            have hΔ0 : 0 < Δ := by linarith
            obtain ⟨c, hc⟩ : ∃ c, c = (wb 0 - pm 0) / Δ := ⟨_, rfl⟩
            rw [← hc] at hrep
            set D : Fin (d+1) → ℝ := Δ⁻¹ • (pp - pm) with hD
            have hD0 : D 0 = 1 := by
              simp only [D, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; rw [← hΔ]; exact inv_mul_cancel₀ hΔ0.ne'
            have hWline : ∀ e, pm 0 - wb 0 ≤ e → e ≤ pp 0 - wb 0 → wb + e • D ∈ B i := by
              intro e he1 he2
              have ee : wb + e • D = pm + (c + e / Δ) • (pp - pm) := by
                rw [hrep]; simp only [D]; rw [smul_smul, add_smul]; abel_nf; rw [div_eq_mul_inv]
              have hc' : c + e / Δ = (wb 0 - pm 0 + e) / Δ := by rw [hc]; ring
              rw [ee]
              refine (hBc i).starConvex hpm |>.add_smul_sub_mem hpp ?_ ?_
              · rw [hc']; exact div_nonneg (by linarith) hΔ0.le
              · rw [hc']; exact (div_le_one hΔ0).2 (by linarith)
            set r := min (wb 0 - pm 0) (pp 0 - wb 0) with hr
            have hr0 : 0 < r := lt_min (by linarith) (by linarith)
            set e0 := xc hpn δ.1 i with he0
            set c' := r / (|e0| + r) with hc'
            have hpos : 0 < |e0| + r := by positivity
            have hc'0 : 0 < c' := div_pos hr0 hpos
            have hc'1 : c' ≤ 1 := (div_le_one hpos).2 (by linarith [abs_nonneg e0])
            have hc'e : c' * |e0| ≤ r := by
              rw [hc', div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith [abs_nonneg e0]
            have hz1 : z + c' • δ ∈ BEF hpn P B := by
              have := hQc.starConvex hzQ |>.add_smul_sub_mem h1 hc'0.le hc'1
              have e : z + c' • (z + δ - z) = z + c' • δ := by module
              rwa [e] at this
            have hz2 : z + (-(c' • δ)) ∈ BEF hpn P B := by
              have := hQc.starConvex hzQ |>.add_smul_sub_mem h2 hc'0.le hc'1
              have e : z + c' • (z - δ - z) = z + (-(c' • δ)) := by module
              rwa [e] at this
            let Φ : Pt n p d → Pt n p d := fun γ =>
              (γ.1, Function.update γ.2 i (fun h => xc hpn γ.1 i * D h.succ))
            have hΦ : ∀ γ : Pt n p d, z + γ ∈ BEF hpn P B → |xc hpn γ.1 i| ≤ r →
                zb + Φ γ ∈ BEF hpn P B := by
              intro γ hγ hrγ
              obtain ⟨hx, hy, hbl⟩ := hγ
              have hab := abs_le.1 hrγ
              have hW := hWline (xc hpn γ.1 i) (by linarith [min_le_left (wb 0 - pm 0) (pp 0 - wb 0)])
                (by linarith [min_le_right (wb 0 - pm 0) (pp 0 - wb 0)])
              have hblkW : block hpn (zb + Φ γ) i = wb + (xc hpn γ.1 i) • D := by
                funext m; refine Fin.cases ?_ (fun h => ?_) m
                · simp only [block, Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD0, mul_one, wb]
                  simp [xc, Φ]
                · simp [block, Φ, wb]
              refine ⟨hx, fun i' h => ?_, fun i' => ?_⟩
              · by_cases hi : i' = i
                · subst hi
                  have := hBy _ hW h
                  have e : (zb + Φ γ).2 i' h = (wb + (xc hpn γ.1 i') • D) h.succ := by
                    rw [← hblkW]; rfl
                  rw [e]; exact this
                · have := hy i' h
                  simpa [Φ, z, Function.update_of_ne hi] using this
              · by_cases hi : i' = i
                · subst hi; rw [hblkW]; exact hW
                · have := hbl i'
                  convert this using 1
                  funext m; refine Fin.cases ?_ (fun h => ?_) m
                  · simp [block, Φ, z, xc]
                  · simp [block, Φ, z, Function.update_of_ne hi]
            have hΦneg : ∀ γ, Φ (-γ) = -Φ γ := by
              intro γ
              refine Prod.ext rfl (funext fun i' => funext fun h => ?_)
              by_cases hi : i' = i
              · subst hi; simp [Φ, xc]
              · simp [Φ, Function.update_of_ne hi]
            have habs : |xc hpn (c' • δ).1 i| ≤ r := by
              have : xc hpn (c' • δ).1 i = c' * e0 := rfl
              rw [this, abs_mul, abs_of_pos hc'0]; exact hc'e
            have habs' : |xc hpn (-(c' • δ)).1 i| ≤ r := by
              have : xc hpn (-(c' • δ)).1 i = -xc hpn (c' • δ).1 i := rfl
              rw [this, abs_neg]; exact habs
            have hA1 := hΦ _ hz1 habs
            have hA2 := hΦ _ hz2 habs'
            rw [hΦneg, ← sub_eq_add_neg] at hA2
            have hΦ0 : Φ (c' • δ) = 0 := ((hpert _ zb hQc).1 (hz j)).2 _ hA1 hA2
            have hδx : (c' • δ).1 = 0 := congrArg Prod.fst hΦ0
            have hδy : ∀ i', i' ≠ i → (c' • δ).2 i' = 0 := by
              intro i' hi
              have := congrFun (congrArg Prod.snd hΦ0) i'
              simpa [Φ, Function.update_of_ne hi] using this
            set g := (c' • δ).2 i with hg
            have hvp : ∀ σ : ℝ, z + σ • (c' • δ) ∈ BEF hpn P B →
                v + σ • (Fin.cons 0 g : Fin (d+1) → ℝ) ∈ B i ∩ {q : Fin (d+1) → ℝ | q 0 = xc hpn (zbar j).1 i} := by
              intro σ hσ
              have e : block hpn (z + σ • (c' • δ)) i = v + σ • (Fin.cons 0 g : Fin (d+1) → ℝ) := by
                funext m; refine Fin.cases ?_ (fun h => ?_) m
                · have : (c' • δ).1 (Fin.castLE hpn i) = 0 := by rw [hδx]; rfl
                  simp [block, z, xc, hv0, hzb] at this ⊢
                  simp [this]
                · simp [block, z, g]
              refine ⟨e ▸ hσ.2.2 i, ?_⟩
              show (v + σ • (Fin.cons 0 g : Fin (d+1) → ℝ)) 0 = _
              simp [hv0, hzb]
            have hp1 := hvp 1 (by simpa using hz1)
            have hp2 := hvp (-1) (by simpa using hz2)
            have hg0 : (Fin.cons 0 g : Fin (d+1) → ℝ) = 0 :=
              ((hpert _ v hSconv).1 hvS).2 _ (by simpa using hp1) (by simpa [sub_eq_add_neg] using hp2)
            have hg' : g = 0 := by
              funext h; have := congrFun hg0 h.succ; simpa using this
            have hδ0 : c' • δ = 0 := by
              refine Prod.ext hδx (funext fun i' => ?_)
              by_cases hi : i' = i
              · subst hi; rw [← hg, hg']; rfl
              · exact hδy i' hi
            rcases smul_eq_zero.1 hδ0 with h | h
            · exact absurd h hc'0.ne'
            · exact h
          have := hH z hzext (fun h hh => by
            have e : z.2 i h = v h.succ := by simp [z]
            rw [e, hvT.1.2 h hh]; exact hwb h hh) j
          have e : xc hpn z.1 i = xc hpn (zbar j).1 i := rfl
          rw [e] at this
          rcases this with h | h <;> linarith [hzi j]
        have hlift : ∀ l' : List (Fin (d+1)), (∀ x ∈ l', x ∈ yCoords d) →
            ∃ l : List (Fin d), l.map Fin.succ = l' := by
          intro l'
          induction l' with
          | nil => intro _; exact ⟨[], rfl⟩
          | cons x l' ih =>
            intro hY
            obtain ⟨l, hl⟩ := ih (fun y hy => hY y (List.mem_cons_of_mem _ hy))
            obtain ⟨h, rfl⟩ := hYsucc x (hY x List.mem_cons_self)
            exact ⟨h :: l, by simp [hl]⟩
        unfold lpr
        congr 1
        ext t
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨l, hlen, hHl⟩
          have hY : ∀ x ∈ l.map Fin.succ, x ∈ yCoords d := by
            intro x hx; obtain ⟨h, _, rfl⟩ := List.mem_map.1 hx; exact hsuccY h
          refine ⟨l.map Fin.succ, hY, by simp [hlen], (hLN _ hY).2 ?_⟩
          intro j w hw hw0 hb
          exact hHN l hHl j w hw hw0 (fun h hh => hb h.succ (List.mem_map_of_mem hh))
        · rintro ⟨l', hY, hlen, hL⟩
          obtain ⟨l, rfl⟩ := hlift l' hY
          refine ⟨l, by simpa using hlen, hNH l ?_⟩
          intro j w hw hw0 hb
          exact (hLN _ hY).1 hL j w hw hw0 (fun h' hh' => by
            obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hh'; exact hb h hh)
