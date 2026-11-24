-- Prove2me | solution 1 for DelaunayStretch.lemma_A_2_segment_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:05:53.770719+00:00
-- url     : https://prove2.me/submissions/7131c706-c00a-4103-a5e0-8171f2025df0

import Theorems.Thm_DelaunayStretch_lemma_A_1_faces
open Set DelaunayStretch

namespace LemA2

theorem tiling {ι : Type*} [Nonempty ι] (P : Finset ι) (J : ι → Set ℝ) (a b : ι → ℝ)
    (hJ : ∀ F ∈ P, J F = Icc (a F) (b F)) (hab : ∀ F ∈ P, a F < b F)
    (hcov : ⋃ F ∈ P, J F = Icc 0 1)
    (hdisj : ∀ F ∈ P, ∀ G ∈ P, F ≠ G → (J F ∩ J G).Subsingleton) :
    ∃ (m : ℕ) (f : ℕ → ι) (t : ℕ → ℝ), 1 ≤ m ∧ (∀ i, 1 ≤ i → i ≤ m → f i ∈ P) ∧
      (∀ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → i ≠ j → f i ≠ f j) ∧ t 0 = 0 ∧ t m = 1 ∧
      (∀ i, i < m → t i < t (i + 1)) ∧
      (∀ i, 1 ≤ i → i ≤ m → J (f i) = Icc (t (i - 1)) (t i)) := by
  classical
  have hsub : ∀ F ∈ P, J F ⊆ Icc 0 1 := fun F hF => by
    rw [← hcov]; exact subset_biUnion_of_mem (u := J) hF
  have haJ : ∀ F ∈ P, a F ∈ J F := fun F hF => by
    rw [hJ F hF]; exact ⟨le_rfl, (hab F hF).le⟩
  have hbJ : ∀ F ∈ P, b F ∈ J F := fun F hF => by
    rw [hJ F hF]; exact ⟨(hab F hF).le, le_rfl⟩
  have ha0 : ∀ F ∈ P, 0 ≤ a F := fun F hF => (hsub F hF (haJ F hF)).1
  have hb1 : ∀ F ∈ P, b F ≤ 1 := fun F hF => (hsub F hF (hbJ F hF)).2
  have hmemJ : ∀ F ∈ P, ∀ x, x ∈ J F ↔ a F ≤ x ∧ x ≤ b F := fun F hF x => by
    rw [hJ F hF]; rfl
  have key : ∀ F ∈ P, ∀ G ∈ P, ∀ x y, x ≠ y → x ∈ J F → x ∈ J G → y ∈ J F → y ∈ J G →
      F = G := by
    intro F hF G hG x y hxy hxF hxG hyF hyG
    by_contra hne
    exact hxy (hdisj F hF G hG hne ⟨hxF, hxG⟩ ⟨hyF, hyG⟩)
  have ainj : Set.InjOn a P := by
    intro F hF G hG h
    refine key F hF G hG (a F) (min (b F) (b G)) ?_ (haJ F hF) ?_ ?_ ?_
    · have h1 := hab F hF; have h2 := hab G hG
      exact ne_of_lt (lt_min h1 (by rw [h]; exact h2))
    · rw [h]; exact haJ G hG
    · rw [hmemJ F hF]; have := hab G hG; constructor
      · exact le_min (hab F hF).le (h ▸ this.le)
      · exact min_le_left _ _
    · rw [hmemJ G hG]; have := hab F hF; constructor
      · exact le_min (h ▸ this.le) (hab G hG).le
      · exact min_le_right _ _
  -- covering lemma
  have hcover : ∀ s ∈ Icc (0:ℝ) 1, ∃ G ∈ P, s ∈ J G := by
    intro s hs
    rw [← hcov] at hs
    simpa using hs
  have K : ∀ F ∈ P, ∀ s ∈ Icc (0:ℝ) 1, b F < s → ∃ G ∈ P, a F < a G ∧ a G ≤ s := by
    intro F hF s hs hbs
    obtain ⟨G, hG, hsG⟩ := hcover s hs
    rw [hmemJ G hG] at hsG
    refine ⟨G, hG, ?_, hsG.1⟩
    by_contra hle
    push Not at hle
    have hFG : F ≠ G := by
      rintro rfl; linarith [hsG.2]
    apply hFG
    refine key F hF G hG (a F) (b F) (ne_of_lt (hab F hF)) (haJ F hF) ?_ (hbJ F hF) ?_
    · rw [hmemJ G hG]; constructor <;> linarith [hab F hF]
    · rw [hmemJ G hG]; constructor <;> linarith [hab F hF]
  set A := P.image a with hAdef
  set m := P.card with hmdef
  have hA : A.card = m := Finset.card_image_of_injOn ainj
  have hm : 1 ≤ m := by
    obtain ⟨G, hG, -⟩ := hcover 0 ⟨le_rfl, zero_le_one⟩
    exact Finset.card_pos.mpr ⟨G, hG⟩
  set g := A.orderEmbOfFin hA with hgdef
  have hgA : ∀ k, ∃ F ∈ P, a F = g k := by
    intro k
    have := A.orderEmbOfFin_mem hA k
    rw [Finset.mem_image] at this
    exact this
  choose φ hφP hφa using hgA
  let gg : ℕ → ℝ := fun i => g ⟨min i (m - 1), by omega⟩
  let ff : ℕ → ι := fun i => φ ⟨min i (m - 1), by omega⟩
  have hffP : ∀ i, ff i ∈ P := fun i => hφP _
  have hffa : ∀ i, a (ff i) = gg i := fun i => hφa _
  have hgg_mono : ∀ i j, i ≤ j → gg i ≤ gg j := by
    intro i j hij
    apply g.monotone
    show min i (m - 1) ≤ min j (m - 1)
    omega
  have hgg_smono : ∀ i j, i < j → j < m → gg i < gg j := by
    intro i j hij hj
    apply g.strictMono
    show min i (m - 1) < min j (m - 1)
    omega
  have hgg_lt : ∀ i j, gg i < gg j → i < j := by
    intro i j h
    by_contra hc
    push Not at hc
    exact absurd (hgg_mono j i hc) (not_le.mpr h)
  have hAall : ∀ G ∈ P, ∃ k, k < m ∧ a G = gg k := by
    intro G hG
    have : a G ∈ (A : Set ℝ) := by
      simp only [hAdef, Finset.coe_image]; exact mem_image_of_mem a hG
    rw [← Finset.range_orderEmbOfFin A hA] at this
    obtain ⟨k, hk⟩ := this
    refine ⟨k.1, k.2, ?_⟩
    rw [← hk]
    show g k = g ⟨min k.1 (m - 1), _⟩
    congr 1
    ext
    simp only
    have := k.2
    omega
  have C0 : gg 0 = 0 := by
    obtain ⟨G, hG, h0G⟩ := hcover 0 ⟨le_rfl, zero_le_one⟩
    rw [hmemJ G hG] at h0G
    have haG : a G = 0 := le_antisymm h0G.1 (ha0 G hG)
    obtain ⟨k, -, hk⟩ := hAall G hG
    apply le_antisymm
    · rw [← haG, hk]; exact hgg_mono 0 k (Nat.zero_le _)
    · rw [← hffa 0]; exact ha0 _ (hffP 0)
  let t : ℕ → ℝ := fun i => if i < m then gg i else 1
  have C1 : ∀ i, i < m → b (ff i) = t (i + 1) := by
    intro i hi
    set F := ff i
    have hF := hffP i
    have haF : a F = gg i := hffa i
    by_cases hi1 : i + 1 < m
    · have ht : t (i + 1) = gg (i + 1) := if_pos hi1
      rw [ht]
      set G := ff (i + 1)
      have hG := hffP (i + 1)
      have haG : a G = gg (i + 1) := hffa (i + 1)
      have hlt : gg i < gg (i + 1) := hgg_smono i (i + 1) (by omega) hi1
      rcases lt_trichotomy (gg (i + 1)) (b F) with h | h | h
      · exfalso
        have habG := hab G hG
        have hFG : F = G := by
          refine key F hF G hG (gg (i + 1)) (min (b F) (b G)) ?_ ?_ ?_ ?_ ?_
          · exact ne_of_lt (lt_min h (haG ▸ habG))
          · rw [hmemJ F hF]; constructor <;> linarith
          · rw [hmemJ G hG]; constructor <;> linarith
          · rw [hmemJ F hF]; constructor
            · exact le_trans (by linarith) (le_min h.le (haG ▸ habG.le))
            · exact min_le_left _ _
          · rw [hmemJ G hG]; constructor
            · exact haG ▸ le_min h.le (haG ▸ habG.le)
            · exact min_le_right _ _
        have := congrArg a hFG
        rw [haF, haG] at this
        linarith
      · exact h.symm
      · exfalso
        have hb0 : 0 ≤ b F := by linarith [ha0 F hF, hab F hF]
        have hg1 : gg (i + 1) ≤ 1 := by rw [← haG]; linarith [hb1 G hG, hab G hG]
        obtain ⟨G', hG', h1, h2⟩ := K F hF ((b F + gg (i + 1)) / 2)
          ⟨by linarith, by linarith⟩ (by linarith)
        obtain ⟨k, hk, hk'⟩ := hAall G' hG'
        rw [haF, hk'] at h1
        rw [hk'] at h2
        have := hgg_lt i k h1
        have := hgg_lt k (i + 1) (by linarith)
        omega
    · have hm' : i + 1 = m := by omega
      have ht : t (i + 1) = 1 := if_neg hi1
      rw [ht]
      apply le_antisymm (hb1 F hF)
      by_contra hlt
      push Not at hlt
      obtain ⟨G', hG', h1, -⟩ := K F hF 1 ⟨zero_le_one, le_rfl⟩ hlt
      obtain ⟨k, hk, hk'⟩ := hAall G' hG'
      rw [haF, hk'] at h1
      have := hgg_lt i k h1
      omega
  refine ⟨m, fun i => ff (i - 1), t, hm, fun i _ _ => hffP _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi1 him hj1 hjm hij hfij
    have := congrArg a hfij
    simp only [hffa] at this
    rcases lt_or_gt_of_ne hij with h | h
    · exact absurd this (ne_of_lt (hgg_smono _ _ (by omega) (by omega)))
    · exact absurd this (ne_of_gt (hgg_smono _ _ (by omega) (by omega)))
  · show (if 0 < m then gg 0 else 1) = 0
    rw [if_pos (by omega), C0]
  · show (if m < m then gg m else 1) = 1
    rw [if_neg (lt_irrefl m)]
  · intro i hi
    rw [← C1 i hi]
    have : t i = gg i := if_pos hi
    rw [this, ← hffa i]
    exact hab _ (hffP i)
  · intro i hi1 him
    simp only
    rw [hJ _ (hffP _), hffa, C1 (i - 1) (by omega)]
    have : t (i - 1) = gg (i - 1) := if_pos (by omega)
    rw [this, Nat.sub_add_cancel hi1]

theorem vertex_of_mem_conv {S : Finset ℂ} {D : Finset (Finset ℂ)} (hD : IsDelaunayTriangulation S D)
    {T : Finset ℂ} (hT : T ∈ D) {s : ℂ} (hs : s ∈ S) (hsc : s ∈ convexHull ℝ (T : Set ℂ)) :
    s ∈ T := by
  classical
  obtain ⟨T'', hT'', hsT''⟩ := hD.2.2.1 s hs
  by_cases hTT : T = T''
  · subst hTT; exact hsT''
  by_contra hsT
  have hint := hD.2.2.2.1 T hT T'' hT'' hTT
  have hs2 : s ∈ convexHull ℝ ((T : Set ℂ) ∩ T'') := by
    rw [← hint]; exact ⟨hsc, subset_convexHull ℝ _ hsT''⟩
  have hsub : (T : Set ℂ) ∩ T'' ⊆ ((T''.erase s : Finset ℂ) : Set ℂ) := by
    intro z ⟨hz1, hz2⟩
    rw [Finset.coe_erase]
    refine ⟨hz2, ?_⟩
    rintro rfl
    exact hsT hz1
  have hs3 : s ∈ affineSpan ℝ ((T''.erase s : Finset ℂ) : Set ℂ) :=
    convexHull_subset_affineSpan _ (convexHull_mono hsub hs2)
  have hcard : (T''.erase s).card = 2 := by
    rw [Finset.card_erase_of_mem hsT'', (hD.1 T'' hT'').1]
  obtain ⟨b, c, -, hbc⟩ := Finset.card_eq_two.mp hcard
  have hcol : Collinear ℝ (insert s ((T''.erase s : Finset ℂ) : Set ℂ)) := by
    rw [collinear_insert_iff_of_mem_affineSpan hs3, hbc]
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact collinear_pair ℝ b c
  apply (hD.1 T'' hT'').2.1
  have : (T'' : Set ℂ) = insert s ((T''.erase s : Finset ℂ) : Set ℂ) := by
    rw [← Finset.coe_insert, Finset.insert_erase hsT'']
  rw [this]; exact hcol

theorem edge_no_S {S : Finset ℂ} {D : Finset (Finset ℂ)} (hD : IsDelaunayTriangulation S D)
    {x y : ℂ} (h : IsEdgeOf D x y) : ∀ s ∈ S, s ∉ openSegment ℝ x y := by
  classical
  obtain ⟨hxy, T, hT, hx, hy⟩ := h
  intro s hs hso
  have hsc : s ∈ convexHull ℝ (T : Set ℂ) :=
    segment_subset_convexHull (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy)
      (openSegment_subset_segment ℝ x y hso)
  have hsT := vertex_of_mem_conv hD hT hs hsc
  have hsx : s ≠ x := by
    rintro rfl; exact hxy (left_mem_openSegment_iff.mp hso)
  have hsy : s ≠ y := by
    rintro rfl; exact hxy (right_mem_openSegment_iff.mp hso)
  have hsub : ({x, s, y} : Finset ℂ) ⊆ T := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hc3 : ({x, s, y} : Finset ℂ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hsy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hsx h.symm, hxy⟩
  have hTeq : ({x, s, y} : Finset ℂ) = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hc3, (hD.1 T hT).1])
  apply (hD.1 T hT).2.1
  rw [← hTeq]
  simp only [Finset.coe_insert, Finset.coe_singleton]
  exact (mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ x y hso)).collinear

theorem real_overlap (a b s₁ s₂ : ℝ) (hab : a ≠ b) (ha : a ∉ Ioo (0:ℝ) 1) (hb : b ∉ Ioo (0:ℝ) 1)
    (h0 : (0:ℝ) ∉ openSegment ℝ a b) (h1 : (1:ℝ) ∉ openSegment ℝ a b)
    (hs₁ : s₁ ∈ segment ℝ a b) (hs₂ : s₂ ∈ segment ℝ a b) (hs₁' : s₁ ∈ Icc (0:ℝ) 1)
    (hs₂' : s₂ ∈ Icc (0:ℝ) 1) (hne : s₁ ≠ s₂) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rw [openSegment_eq_Ioo' hab] at h0 h1
  rw [segment_eq_uIcc] at hs₁ hs₂
  simp only [mem_Ioo, not_and_or, not_lt] at ha hb h0 h1
  obtain ⟨hs₁a, hs₁b⟩ := hs₁'
  obtain ⟨hs₂a, hs₂b⟩ := hs₂'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hs₁ hs₂
      rw [min_eq_left h, max_eq_right h] at h0 h1
      obtain ⟨h11, h12⟩ := hs₁; obtain ⟨h21, h22⟩ := hs₂
      left
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases h0 with h0 | h0 <;>
        rcases h1 with h1 | h1 <;> constructor <;> linarith
    · rw [uIcc_of_ge h] at hs₁ hs₂
      rw [min_eq_right h, max_eq_left h] at h0 h1
      obtain ⟨h11, h12⟩ := hs₁; obtain ⟨h21, h22⟩ := hs₂
      right
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases h0 with h0 | h0 <;>
        rcases h1 with h1 | h1 <;> constructor <;> linarith
  · rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hs₁ hs₂
      rw [min_eq_left h, max_eq_right h] at h0 h1
      obtain ⟨h11, h12⟩ := hs₁; obtain ⟨h21, h22⟩ := hs₂
      left
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases h0 with h0 | h0 <;>
        rcases h1 with h1 | h1 <;> constructor <;> linarith
    · rw [uIcc_of_ge h] at hs₁ hs₂
      rw [min_eq_right h, max_eq_left h] at h0 h1
      obtain ⟨h11, h12⟩ := hs₁; obtain ⟨h21, h22⟩ := hs₂
      right
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases h0 with h0 | h0 <;>
        rcases h1 with h1 | h1 <;> constructor <;> linarith

theorem lineMap_C (x y : ℂ) (c : ℝ) :
    (AffineMap.lineMap x y c : ℂ) = x + (c : ℂ) * (y - x) := by
  rw [AffineMap.lineMap_apply_module, Complex.real_smul, Complex.real_smul]
  push_cast; ring

theorem on_line_of_two {u v x y p q : ℂ} (hp : p ∈ segment ℝ x y ∩ segment ℝ u v)
    (hq : q ∈ segment ℝ x y ∩ segment ℝ u v) (hpq : p ≠ q) :
    ∃ a b : ℝ, AffineMap.lineMap u v a = x ∧ AffineMap.lineMap u v b = y := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap] at hp hq
  obtain ⟨⟨α, -, hα⟩, ⟨s₁, -, hs₁⟩⟩ := hp
  obtain ⟨⟨β, -, hβ⟩, ⟨s₂, -, hs₂⟩⟩ := hq
  rw [lineMap_C] at hα hβ hs₁ hs₂
  have hne : (β : ℂ) - α ≠ 0 := by
    intro h
    apply hpq
    have : (β : ℂ) = α := by linear_combination h
    rw [← hα, ← hβ, this]
  set c : ℝ := (s₂ - s₁) / (β - α)
  have hc : (c : ℂ) * (β - α) = s₂ - s₁ := by
    simp only [c]; push_cast; field_simp
  have hyx : y - x = (c : ℂ) * (v - u) := by
    apply mul_left_cancel₀ hne
    linear_combination (hβ - hα) - (hs₂ - hs₁) - (v - u) * hc
  refine ⟨s₁ - α * c, s₁ - α * c + c, ?_, ?_⟩
  · rw [lineMap_C]; push_cast
    linear_combination -(hα - hs₁ - (α : ℂ) * hyx)
  · rw [lineMap_C]; push_cast
    linear_combination -(hα - hs₁ - (α : ℂ) * hyx + hyx)


theorem overlap {u v x y : ℂ} (huv : u ≠ v) (hxy : x ≠ y) (hxS : x ∉ openSegment ℝ u v)
    (hyS : y ∉ openSegment ℝ u v) (huS : u ∉ openSegment ℝ x y) (hvS : v ∉ openSegment ℝ x y)
    {p q : ℂ} (hp : p ∈ segment ℝ x y ∩ segment ℝ u v) (hq : q ∈ segment ℝ x y ∩ segment ℝ u v)
    (hpq : p ≠ q) : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  obtain ⟨a, b, rfl, rfl⟩ := on_line_of_two hp hq hpq
  set L : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap u v with hL
  have hinj : Function.Injective L := AffineMap.lineMap_injective ℝ huv
  have hab : a ≠ b := fun h => hxy (by rw [h])
  have hnI : ∀ c : ℝ, L c ∉ openSegment ℝ u v → c ∉ Ioo (0:ℝ) 1 := fun c hc h =>
    hc (by rw [openSegment_eq_image_lineMap]; exact mem_image_of_mem _ h)
  have hnO : ∀ c : ℝ, L c ∉ openSegment ℝ (L a) (L b) → c ∉ openSegment ℝ a b := fun c hc h =>
    hc (by rw [← image_openSegment]; exact mem_image_of_mem _ h)
  have hL0 : L 0 = u := AffineMap.lineMap_apply_zero _ _
  have hL1 : L 1 = v := AffineMap.lineMap_apply_one _ _
  have hseg : ∀ z ∈ segment ℝ (L a) (L b) ∩ segment ℝ u v,
      ∃ s, s ∈ segment ℝ a b ∧ s ∈ Icc (0:ℝ) 1 ∧ L s = z := by
    rintro z ⟨hz1, hz2⟩
    rw [← image_segment] at hz1
    rw [segment_eq_image_lineMap] at hz2
    obtain ⟨s, hs, rfl⟩ := hz1
    obtain ⟨s', hs', hss'⟩ := hz2
    refine ⟨s, hs, ?_, rfl⟩
    have : s' = s := hinj hss'
    rw [← this]; exact hs'
  obtain ⟨s₁, h11, h12, rfl⟩ := hseg p hp
  obtain ⟨s₂, h21, h22, rfl⟩ := hseg q hq
  have hs : s₁ ≠ s₂ := fun h => hpq (by rw [h])
  rcases real_overlap a b s₁ s₂ hab (hnI a hxS) (hnI b hyS) (hnO 0 (by rwa [hL0]))
      (hnO 1 (by rwa [hL1])) h11 h21 h12 h22 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; exact ⟨hL0, hL1⟩
  · right; exact ⟨hL1, hL0⟩

theorem faceEdge_meet {S : Finset ℂ} {D : Finset (Finset ℂ)} (hD : IsDelaunayTriangulation S D)
    {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hopen : ∀ p ∈ S, p ∉ openSegment ℝ u v) (hnot : ¬ IsEdgeOf D u v)
    {F : Set ℂ} (hF : IsFace S D F) {x y : ℂ} (he : IsFaceEdge F x y) :
    (segment ℝ x y ∩ segment ℝ u v).Subsingleton := by
  have hE : IsEdgeOf D x y := (lemma_A_1_faces S D hD).2.2.1 F hF x y he
  have hE' := hE
  obtain ⟨hxy, T, hT, hx, hy⟩ := hE'
  have hxS : x ∈ S := (hD.1 T hT).2.2 hx
  have hyS : y ∈ S := (hD.1 T hT).2.2 hy
  have hno := edge_no_S hD hE
  intro p hp q hq
  by_contra hpq
  rcases overlap huv hxy (hopen x hxS) (hopen y hyS) (hno u hu) (hno v hv) hp hq hpq with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hnot hE
  · exact hnot ⟨huv, T, hT, hy, hx⟩

theorem extreme_subset_S {S : Finset ℂ} {D : Finset (Finset ℂ)} (hD : IsDelaunayTriangulation S D)
    {F : Set ℂ} (hF : IsFace S D F) {p : ℂ} (hp : p ∈ Set.extremePoints ℝ F) : p ∈ S := by
  obtain ⟨T, hT, rfl⟩ := hF
  rw [((lemma_A_1_faces S D hD).1 T hT).1] at hp
  exact hp.1

theorem mem_extreme_of_mem_face {S : Finset ℂ} {D : Finset (Finset ℂ)}
    (hD : IsDelaunayTriangulation S D) {T : Finset ℂ} (hT : T ∈ D) {s : ℂ} (hs : s ∈ S)
    (hsF : s ∈ face S T) : s ∈ Set.extremePoints ℝ (face S T) := by
  have hA := (lemma_A_1_faces S D hD).1 T hT
  rw [hA.1]
  refine ⟨hs, ?_⟩
  rw [← hA.2.2] at hsF
  simp only [mem_iUnion] at hsF
  obtain ⟨T', hT', hcirc, hsT'⟩ := hsF
  have hsT'' := vertex_of_mem_conv hD hT' hs hsT'
  rw [← hcirc]
  obtain ⟨o, r, hor, -⟩ := hD.2.2.2.2 T' hT'
  exact ⟨o, r, hor, hor s hsT''⟩

theorem eq_Icc_of (K : Set ℝ) (hc : IsClosed K) (hcv : Convex ℝ K) (hb : K ⊆ Icc 0 1)
    (hne : K.Nonempty) : K = Icc (sInf K) (sSup K) := by
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hc hb
  apply Subset.antisymm
  · intro x hx
    exact ⟨csInf_le hK.bddBelow hx, le_csSup hK.bddAbove hx⟩
  · have h1 := hK.sInf_mem hne
    have h2 := hK.sSup_mem hne
    have hle : sInf K ≤ sSup K := csInf_le_csSup hne hK.bddBelow hK.bddAbove
    rw [← segment_eq_Icc hle]
    exact hcv.segment_subset h1 h2

end LemA2

open LemA2 in
theorem solution (S : Finset ℂ) (D : Finset (Finset ℂ))
    (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hopen : ∀ p ∈ S, p ∉ openSegment ℝ u v) (hnot : ¬ IsEdgeOf D u v) :
    ∃ (m : ℕ) (F : ℕ → Set ℂ) (t : ℕ → ℝ) (e e' : ℕ → ℂ),
      1 ≤ m ∧
      (∀ i, 1 ≤ i → i ≤ m → IsFace S D (F i)) ∧
      (∀ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → i ≠ j → F i ≠ F j) ∧
      t 0 = 0 ∧ t m = 1 ∧ (∀ i, i < m → t i < t (i + 1)) ∧
      (∀ i, 1 ≤ i → i ≤ m →
        segment ℝ u v ∩ F i =
          segment ℝ (AffineMap.lineMap u v (t (i - 1))) (AffineMap.lineMap u v (t i))) ∧
      (∀ i, 1 ≤ i → i + 1 ≤ m →
        IsFaceEdge (F i) (e i) (e' i) ∧ IsFaceEdge (F (i + 1)) (e i) (e' i) ∧
          AffineMap.lineMap u v (t i) ∈ openSegment ℝ (e i) (e' i) ∧
          ¬ (e i ∈ line[ℝ, u, v] ∧ e' i ∈ line[ℝ, u, v])) ∧
      u ∈ Set.extremePoints ℝ (F 1) ∧ v ∈ Set.extremePoints ℝ (F m) ∧
      (∀ i, 2 ≤ i → i + 1 ≤ m →
        segment ℝ (e (i - 1)) (e' (i - 1)) ≠ segment ℝ (e i) (e' i)) := by
  classical
  have hA1 := lemma_A_1_faces S D hD
  set L : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap u v with hL
  have hinj : Function.Injective L := AffineMap.lineMap_injective ℝ huv
  have hL0 : L 0 = u := AffineMap.lineMap_apply_zero _ _
  have hL1 : L 1 = v := AffineMap.lineMap_apply_one _ _
  have Lseg : ∀ s ∈ Icc (0:ℝ) 1, L s ∈ segment ℝ u v := fun s hs => by
    rw [segment_eq_image_lineMap]; exact mem_image_of_mem _ hs
  let FS : Finset (Set ℂ) := D.image (face S)
  have hFS : ∀ F, F ∈ FS ↔ IsFace S D F := by
    intro F
    simp only [FS, Finset.mem_image, IsFace]
    constructor
    · rintro ⟨T, hT, rfl⟩; exact ⟨T, hT, rfl⟩
    · rintro ⟨T, hT, rfl⟩; exact ⟨T, hT, rfl⟩
  have hFcc : ∀ F, IsFace S D F → IsClosed F ∧ Convex ℝ F := by
    rintro F ⟨T, hT, rfl⟩
    exact ⟨(Set.Finite.isCompact_convexHull ℝ
      ((S.finite_toSet).subset inter_subset_left)).isClosed, convex_convexHull ℝ _⟩
  let J : Set ℂ → Set ℝ := fun F => Icc 0 1 ∩ L ⁻¹' F
  have hsegJ : ∀ F, segment ℝ u v ∩ F = L '' J F := by
    intro F
    rw [segment_eq_image_lineMap, ← image_inter_preimage]
  have hJsub : ∀ F, J F ⊆ Icc 0 1 := fun F => inter_subset_left
  have hJcl : ∀ F, IsFace S D F → IsClosed (J F) := fun F hF =>
    isClosed_Icc.inter ((hFcc F hF).1.preimage AffineMap.lineMap_continuous)
  have hJcv : ∀ F, IsFace S D F → Convex ℝ (J F) := fun F hF =>
    (convex_Icc 0 1).inter ((hFcc F hF).2.affine_preimage L)
  have hJcov : ∀ s ∈ Icc (0:ℝ) 1, ∃ F, IsFace S D F ∧ s ∈ J F := by
    intro s hs
    have h1 : L s ∈ convexHull ℝ (S : Set ℂ) := segment_subset_convexHull hu hv (Lseg s hs)
    rw [← hA1.2.1] at h1
    simp only [mem_iUnion] at h1
    obtain ⟨T, hT, hsT⟩ := h1
    exact ⟨face S T, ⟨T, hT, rfl⟩, hs, hsT⟩
  have hJdisj : ∀ F G, IsFace S D F → IsFace S D G → F ≠ G → (J F ∩ J G).Subsingleton := by
    intro F G hF hG hne s ⟨hsF, hsG⟩ s' ⟨hs'F, hs'G⟩
    apply hinj
    have h1 : L s ∈ F ∩ G := ⟨hsF.2, hsG.2⟩
    have h2 : L s' ∈ F ∩ G := ⟨hs'F.2, hs'G.2⟩
    rcases hA1.2.2.2 F G hF hG hne with h | ⟨p, -, -, h⟩ | ⟨x, y, hx, -, h⟩
    · rw [h] at h1; exact h1.elim
    · rw [h, mem_singleton_iff] at h1 h2; rw [h1, h2]
    · have hss := faceEdge_meet hD hu hv huv hopen hnot hF hx
      rw [h] at h1 h2
      exact hss ⟨h1, Lseg s hsF.1⟩ ⟨h2, Lseg s' hs'F.1⟩
  let P := FS.filter (fun F => ¬ (J F).Subsingleton)
  have hPmem : ∀ F, F ∈ P ↔ IsFace S D F ∧ ¬ (J F).Subsingleton := by
    intro F; simp only [P, Finset.mem_filter, hFS]
  have hJicc : ∀ F ∈ P, J F = Icc (sInf (J F)) (sSup (J F)) := fun F hF => by
    obtain ⟨hF1, hF2⟩ := (hPmem F).1 hF
    exact eq_Icc_of _ (hJcl F hF1) (hJcv F hF1) (hJsub F) (by by_contra hne; exact hF2 (Set.not_nonempty_iff_eq_empty.1 hne ▸ subsingleton_empty))
  have hab : ∀ F ∈ P, sInf (J F) < sSup (J F) := fun F hF => by
    by_contra h
    push Not at h
    exact ((hPmem F).1 hF).2 (by rw [hJicc F hF]; exact subsingleton_Icc_of_ge h)
  have hcov : ⋃ F ∈ P, J F = Icc 0 1 := by
    apply Subset.antisymm
    · exact iUnion₂_subset fun F _ => hJsub F
    · set U := ⋃ F ∈ P, J F with hU
      have hUcl : IsClosed U :=
        isClosed_biUnion_finset (fun F hF => hJcl F ((hPmem F).1 hF).1)
      set N := ⋃ F ∈ FS.filter (fun F => (J F).Subsingleton), J F with hN
      have hNfin : N.Finite := by
        apply Set.Finite.biUnion (Finset.finite_toSet _)
        intro F hF
        exact (Finset.mem_filter.1 hF).2.finite
      have hsub : Icc 0 1 ⊆ U ∪ N := by
        intro s hs
        obtain ⟨F, hF, hsF⟩ := hJcov s hs
        by_cases hsub : (J F).Subsingleton
        · right
          exact mem_biUnion (Finset.mem_filter.2 ⟨(hFS F).2 hF, hsub⟩) hsF
        · left
          exact mem_biUnion ((hPmem F).2 ⟨hF, hsub⟩) hsF
      have hdense : Dense Nᶜ := hNfin.countable.dense_compl ℝ
      have h1 : Ioo (0:ℝ) 1 ⊆ U := by
        intro s hs
        have := hdense.open_subset_closure_inter isOpen_Ioo hs
        refine closure_minimal ?_ hUcl this
        rintro z ⟨hz1, hz2⟩
        rcases hsub (Ioo_subset_Icc_self hz1) with h | h
        · exact h
        · exact absurd h hz2
      rw [← closure_Ioo zero_ne_one]
      exact closure_minimal h1 hUcl
  obtain ⟨m, f, t, hm, hfP, hfinj, ht0, htm, htstep, hfJ⟩ :=
    tiling P J (fun F => sInf (J F)) (fun F => sSup (J F)) hJicc hab hcov
      (fun F hF G hG hne => hJdisj F G ((hPmem F).1 hF).1 ((hPmem G).1 hG).1 hne)
  have hfF : ∀ i, 1 ≤ i → i ≤ m → IsFace S D (f i) := fun i h1 h2 =>
    ((hPmem _).1 (hfP i h1 h2)).1
  have htlt : ∀ j k, j < k → k ≤ m → t j < t k := by
    intro j k hjk hkm
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | h
      · exact (ih h (by omega)).trans (htstep k (by omega))
      · subst h; exact htstep j (by omega)
  have ht01 : ∀ i, i ≤ m → t i ∈ Icc (0:ℝ) 1 := by
    intro i hi
    constructor
    · rcases Nat.eq_zero_or_pos i with h | h
      · rw [h, ht0]
      · rw [← ht0]; exact (htlt 0 i h hi).le
    · rcases eq_or_lt_of_le hi with h | h
      · rw [h, htm]
      · rw [← htm]; exact (htlt i m h le_rfl).le
  have hmemf : ∀ i, 1 ≤ i → i ≤ m → ∀ s, s ∈ Icc (0:ℝ) 1 → L s ∈ f i →
      t (i - 1) ≤ s ∧ s ≤ t i := by
    intro i h1 h2 s hs hsf
    have : s ∈ J (f i) := ⟨hs, hsf⟩
    rw [hfJ i h1 h2] at this
    exact this
  have hLf : ∀ i, 1 ≤ i → i ≤ m → ∀ s, t (i - 1) ≤ s → s ≤ t i → L s ∈ f i := by
    intro i h1 h2 s hs1 hs2
    have : s ∈ J (f i) := by rw [hfJ i h1 h2]; exact ⟨hs1, hs2⟩
    exact this.2
  have hzboth : ∀ i, 1 ≤ i → i + 1 ≤ m → L (t i) ∈ f i ∧ L (t i) ∈ f (i + 1) := by
    intro i hi1 hi2
    refine ⟨hLf i hi1 (by omega) _ (htlt _ _ (by omega) (by omega)).le le_rfl,
      hLf (i + 1) (by omega) hi2 _ (by rw [Nat.add_sub_cancel]) (htlt _ _ (by omega) hi2).le⟩
  have hedge : ∀ i, ∃ x y : ℂ, 1 ≤ i → i + 1 ≤ m →
      IsFaceEdge (f i) x y ∧ IsFaceEdge (f (i + 1)) x y ∧ f i ∩ f (i + 1) = segment ℝ x y ∧
      L (t i) ∈ openSegment ℝ x y ∧ ¬ (x ∈ line[ℝ, u, v] ∧ y ∈ line[ℝ, u, v]) := by
    intro i
    by_cases hi : 1 ≤ i ∧ i + 1 ≤ m
    swap
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hi⟩
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hz1, hz2⟩ := hzboth i hi1 hi2
    have hzo : L (t i) ∈ openSegment ℝ u v := by
      rw [openSegment_eq_image_lineMap]
      refine mem_image_of_mem _ ⟨?_, ?_⟩
      · rw [← ht0]; exact htlt 0 i (by omega) (by omega)
      · rw [← htm]; exact htlt i m (by omega) le_rfl
    have hzS : L (t i) ∉ S := fun h => hopen _ h hzo
    have hne : f i ≠ f (i + 1) := hfinj i (i + 1) hi1 (by omega) (by omega) hi2 (by omega)
    have hFi := hfF i hi1 (by omega)
    rcases hA1.2.2.2 (f i) (f (i + 1)) hFi (hfF (i + 1) (by omega) hi2) hne with
      h | ⟨p, hp, -, h⟩ | ⟨x, y, hx, hy, h⟩
    · exfalso
      have : L (t i) ∈ f i ∩ f (i + 1) := ⟨hz1, hz2⟩
      rw [h] at this; exact this
    · exfalso
      have : L (t i) ∈ f i ∩ f (i + 1) := ⟨hz1, hz2⟩
      rw [h, mem_singleton_iff] at this
      exact hzS (this ▸ extreme_subset_S hD hFi hp)
    · have hxS := extreme_subset_S hD hFi hx.1
      have hyS := extreme_subset_S hD hFi hx.2.1
      have hzo2 : L (t i) ∈ openSegment ℝ x y := by
        refine mem_openSegment_of_ne_left_right (fun e => hzS (e ▸ hxS))
          (fun e => hzS (e ▸ hyS)) ?_
        rw [← h]; exact ⟨hz1, hz2⟩
      refine ⟨x, y, fun _ _ => ⟨hx, hy, h, hzo2, ?_⟩⟩
      rintro ⟨hxl, hyl⟩
      obtain ⟨α, hα⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hxl
      obtain ⟨β, hβ⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hyl
      have hα' : L α = x := hα
      have hβ' : L β = y := hβ
      rw [← hα', ← hβ', ← image_openSegment] at hzo2
      obtain ⟨s, hs, hseq⟩ := hzo2
      have hst : s = t i := hinj hseq
      subst hst
      have hαβ : α ≠ β := fun e => hx.2.2.1 (by rw [← hα', ← hβ', e])
      rw [openSegment_eq_Ioo' hαβ] at hs
      obtain ⟨s', hs'1, hs'2⟩ := exists_between (lt_min hs.2 (htstep _ (by omega)))
      have hs'm1 := min_le_left (max α β) (t (i + 1))
      have hs'm2 := min_le_right (max α β) (t (i + 1))
      have hLs' : L s' ∈ f i := by
        have : L s' ∈ segment ℝ x y := by
          rw [← hα', ← hβ', ← image_segment]
          refine mem_image_of_mem _ ?_
          rw [segment_eq_uIcc]
          exact ⟨by linarith [hs.1], by linarith⟩
        rw [← h] at this; exact this.1
      have h01 := ht01 (i + 1) hi2
      have := hmemf i hi1 (by omega) s'
        ⟨by linarith [(ht01 i (by omega)).1, hs'1], by linarith [h01.2]⟩ hLs'
      linarith [this.2]
  choose e e' he using hedge
  refine ⟨m, f, t, e, e', hm, hfF, hfinj, ht0, htm, htstep, ?_, fun i h1 h2 => ?_, ?_, ?_, ?_⟩
  · intro i h1 h2
    rw [hsegJ, hfJ i h1 h2, ← segment_eq_Icc (htlt _ _ (by omega) h2).le, image_segment]
  · obtain ⟨a1, a2, -, a4, a5⟩ := he i h1 h2
    exact ⟨a1, a2, a4, a5⟩
  · obtain ⟨T, hT, hfT⟩ := hfF 1 le_rfl hm
    have hu1 : u ∈ f 1 := by
      rw [← hL0]
      exact hLf 1 le_rfl hm 0 (by simp [ht0]) (by rw [← ht0]; exact (htstep 0 hm).le)
    rw [hfT] at hu1 ⊢
    exact mem_extreme_of_mem_face hD hT hu hu1
  · obtain ⟨T, hT, hfT⟩ := hfF m hm le_rfl
    have hv1 : v ∈ f m := by
      rw [← hL1]
      exact hLf m hm le_rfl 1 (by rw [← htm]; exact (htlt _ _ (by omega) le_rfl).le)
        (by rw [htm])
    rw [hfT] at hv1 ⊢
    exact mem_extreme_of_mem_face hD hT hv hv1
  · intro i h1 h2 heq
    obtain ⟨-, -, hA, -, -⟩ := he (i - 1) (by omega) (by omega)
    obtain ⟨-, -, hB, -, -⟩ := he i (by omega) h2
    have hi' : i - 1 + 1 = i := by omega
    rw [hi'] at hA
    have hz : L (t i) ∈ f (i - 1) := by
      have : L (t i) ∈ f i ∩ f (i + 1) := hzboth i (by omega) h2
      rw [hB, ← heq, ← hA] at this
      exact this.1
    have := hmemf (i - 1) (by omega) (by omega) (t i) (ht01 i (by omega)) hz
    have h3 := htlt (i - 1) i (by omega) (by omega)
    linarith [this.2]
