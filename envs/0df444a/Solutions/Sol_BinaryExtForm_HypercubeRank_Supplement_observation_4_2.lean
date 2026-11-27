-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.Supplement.observation_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:04.402728+00:00
-- url     : https://prove2.me/submissions/c764d721-f82a-4518-9767-e5afbfe45378

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
    (i : Fin p) (α : Fin ℓ → ℤ) :
    propRank hpn P B i α = sInf {c : ℕ | ∃ Z : Finset (Fin d), Z.card = c ∧
      ∀ z ∈ Set.extremePoints ℝ (BEF hpn P B),
        (∃ j, (α j : ℝ) < xc hpn z.1 i ∧ xc hpn z.1 i < α j + 1) →
          ∃ h ∈ Z, z.2 i h ≠ 0 ∧ z.2 i h ≠ 1} := by
            classical
            have hPc : Convex ℝ P := by
              obtain ⟨S, rfl⟩ := hP
              exact convex_convexHull ℝ _
            have hBc : ∀ q, Convex ℝ (B q) := by
              intro q
              obtain ⟨S, hS⟩ := (hB q).1
              rw [hS]
              exact convex_convexHull ℝ _
            have hblock : ∀ (z w : Pt n p d) (a b : ℝ) (q : Fin p),
                block hpn (a • z + b • w) q = a • block hpn z q + b • block hpn w q := by
              intro z w a b q
              ext j
              refine Fin.cases ?_ (fun t => ?_) j <;> simp [block, xc]
            have hQc : Convex ℝ (BEF hpn P B) := by
              intro z hz w hw a b ha hb hab
              refine ⟨hPc hz.1 hw.1 ha hb hab, ?_, ?_⟩
              · intro q t
                change 0 ≤ a * z.2 q t + b * w.2 q t ∧ a * z.2 q t + b * w.2 q t ≤ 1
                have hz' := hz.2.1 q t
                have hw' := hw.2.1 q t
                constructor <;> nlinarith
              · intro q
                rw [hblock]
                exact hBc q (hz.2.2 q) (hw.2.2 q) ha hb hab
            have hstep : ∀ (S : Set (Pt n p d)), Convex ℝ S →
                (∀ z ∈ S, ∀ j, 0 ≤ z.2 i j ∧ z.2 i j ≤ 1) →
                ∀ (j : Fin d) (z : Pt n p d),
                z ∈ Set.extremePoints ℝ (ySplit S i j) ↔
                  z ∈ Set.extremePoints ℝ S ∧ (z.2 i j = 0 ∨ z.2 i j = 1) := by
              intro S hSc hSb j z
              have hsub : ySplit S i j ⊆ S := convexHull_min Set.inter_subset_left hSc
              constructor
              · intro hz
                have hzm : z ∈ S ∧ (z.2 i j = 0 ∨ z.2 i j = 1) :=
                  extremePoints_convexHull_subset (A := S ∩ {w | w.2 i j = 0 ∨ w.2 i j = 1}) hz
                refine ⟨⟨hzm.1, ?_⟩, hzm.2⟩
                intro x hx y hy hseg
                obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
                have he : a * x.2 i j + b * y.2 i j = z.2 i j :=
                  congrArg (fun t : Pt n p d => t.2 i j) heq
                have hx' := hSb x hx j
                have hy' := hSb y hy j
                have hxy : (x.2 i j = 0 ∨ x.2 i j = 1) ∧ (y.2 i j = 0 ∨ y.2 i j = 1) := by
                  rcases hzm.2 with hzero | hone
                  · constructor <;> left <;> nlinarith
                  · constructor <;> right <;> nlinarith
                exact hz.2 (subset_convexHull ℝ _ ⟨hx, hxy.1⟩)
                  (subset_convexHull ℝ _ ⟨hy, hxy.2⟩) ⟨a, b, ha, hb, hab, heq⟩
              · rintro ⟨hz, hb⟩
                exact ⟨subset_convexHull ℝ _ ⟨hz.1, hb⟩,
                  fun x hx y hy hseg => hz.2 (hsub hx) (hsub hy) hseg⟩
            have hiter : ∀ (l : List (Fin d)) (S : Set (Pt n p d)), Convex ℝ S →
                (∀ z ∈ S, ∀ j, 0 ≤ z.2 i j ∧ z.2 i j ≤ 1) →
                ∀ z, z ∈ Set.extremePoints ℝ (iterYSplit S i l) ↔
                  z ∈ Set.extremePoints ℝ S ∧ ∀ j ∈ l, z.2 i j = 0 ∨ z.2 i j = 1 := by
              intro l
              induction l with
              | nil => intro S hSc hSb z; simp [iterYSplit]
              | cons j l ih =>
                intro S hSc hSb z
                have hsub : ySplit S i j ⊆ S := convexHull_min Set.inter_subset_left hSc
                change z ∈ Set.extremePoints ℝ (iterYSplit (ySplit S i j) i l) ↔ _
                have hc : Convex ℝ (ySplit S i j) := convex_convexHull ℝ _
                rw [ih (ySplit S i j) hc (fun w hw => hSb w (hsub hw)) z,
                  hstep S hSc hSb j z]
                simp only [List.mem_cons, forall_eq_or_imp]
                tauto
            have hgood : ∀ l : List (Fin d),
                SatisfiesP hpn (iterYSplit (BEF hpn P B) i l) i α ↔
                ∀ z ∈ Set.extremePoints ℝ (BEF hpn P B),
                  (∃ j, (α j : ℝ) < xc hpn z.1 i ∧ xc hpn z.1 i < α j + 1) →
                    ∃ h ∈ l.toFinset, z.2 i h ≠ 0 ∧ z.2 i h ≠ 1 := by
              intro l
              have hi := hiter l (BEF hpn P B) hQc (fun z hz j => hz.2.1 i j)
              unfold SatisfiesP
              simp_rw [hi]
              simp only [List.mem_toFinset]
              constructor
              · intro hs z hz hv
                by_contra! hn
                obtain ⟨j, hj, hj'⟩ := hv
                have hbin : ∀ h ∈ l, z.2 i h = 0 ∨ z.2 i h = 1 := by
                  intro h hh
                  by_cases h0 : z.2 i h = 0
                  · exact Or.inl h0
                  · exact Or.inr (hn h hh h0)
                rcases hs z ⟨hz, hbin⟩ j with hle | hle <;> linarith
              · intro hs z hz j
                by_contra! hn
                obtain ⟨h, hh, h0, h1⟩ := hs z hz.1 ⟨j, hn.1, hn.2⟩
                exact (hz.2 h hh).elim h0 h1
            let H : Finset (Fin d) → Prop := fun Z =>
              ∀ z ∈ Set.extremePoints ℝ (BEF hpn P B),
                (∃ j, (α j : ℝ) < xc hpn z.1 i ∧ xc hpn z.1 i < α j + 1) →
                  ∃ h ∈ Z, z.2 i h ≠ 0 ∧ z.2 i h ≠ 1
            let A : Set ℕ := {t | ∃ l : List (Fin d), l.length = t ∧
              SatisfiesP hpn (iterYSplit (BEF hpn P B) i l) i α}
            let C : Set ℕ := {c | ∃ Z : Finset (Fin d), Z.card = c ∧ H Z}
            change sInf A = sInf C
            have hca : ∀ c ∈ C, c ∈ A := by
              intro c hc
              obtain ⟨Z, hZc, hZ⟩ := hc
              refine ⟨Z.toList, ?_, (hgood Z.toList).2 ?_⟩
              · simpa using hZc
              · simpa only [Finset.toList_toFinset] using hZ
            have hac : ∀ t ∈ A, ∃ c ∈ C, c ≤ t := by
              intro t ht
              obtain ⟨l, hlt, hl⟩ := ht
              refine ⟨l.toFinset.card, ⟨l.toFinset, rfl, (hgood l).1 hl⟩, ?_⟩
              exact hlt ▸ l.toFinset_card_le
            by_cases hC : C.Nonempty
            · have hA : A.Nonempty := by
                obtain ⟨c, hc⟩ := hC
                exact ⟨c, hca c hc⟩
              apply le_antisymm
              · exact le_csInf hC (fun c hc => Nat.sInf_le (hca c hc))
              · apply le_csInf hA
                intro t ht
                obtain ⟨c, hc, hct⟩ := hac t ht
                exact (Nat.sInf_le hc).trans hct
            · have hC0 : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
              have hA0 : A = ∅ := by
                apply Set.not_nonempty_iff_eq_empty.mp
                rintro ⟨t, ht⟩
                obtain ⟨c, hc, hct⟩ := hac t ht
                exact hC ⟨c, hc⟩
              rw [hA0, hC0]
