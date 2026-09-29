-- Prove2me | solution 1 for BiconvexProg.BranchBound.vex_bilinear_separable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:27:45.279162+00:00
-- url     : https://prove2.me/submissions/179a6bc4-503c-482d-8dc5-ee662952415b

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

/-- The McCormick function: maximum of the two affine underestimators of `xy` on a rectangle. -/
noncomputable def aux_vbs_hh (l L m M : ℝ) (p : ℝ × ℝ) : ℝ :=
  max (m * p.1 + l * p.2 - l * m) (M * p.1 + L * p.2 - L * M)

lemma aux_vbs_hh_comb (l L m M : ℝ) (p q : ℝ × ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    aux_vbs_hh l L m M (a • p + b • q) ≤ a * aux_vbs_hh l L m M p + b * aux_vbs_hh l L m M q := by
  unfold aux_vbs_hh
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left
    (le_max_left (m * p.1 + l * p.2 - l * m) (M * p.1 + L * p.2 - L * M)) ha
  have h2 := mul_le_mul_of_nonneg_left
    (le_max_right (m * p.1 + l * p.2 - l * m) (M * p.1 + L * p.2 - L * M)) ha
  have h3 := mul_le_mul_of_nonneg_left
    (le_max_left (m * q.1 + l * q.2 - l * m) (M * q.1 + L * q.2 - L * M)) hb
  have h4 := mul_le_mul_of_nonneg_left
    (le_max_right (m * q.1 + l * q.2 - l * m) (M * q.1 + L * q.2 - L * M)) hb
  have hb' : b = 1 - a := by linarith
  subst hb'
  apply max_le
  · linarith
  · linarith

lemma aux_vbs_hh_convexOn (l L m M : ℝ) :
    ConvexOn ℝ (Set.Icc l L ×ˢ Set.Icc m M) (aux_vbs_hh l L m M) := by
  refine ⟨(convex_Icc _ _).prod (convex_Icc _ _), ?_⟩
  intro p _ q _ a b ha hb hab
  simpa [smul_eq_mul] using aux_vbs_hh_comb l L m M p q a b ha hb hab

lemma aux_vbs_hh_le {l L m M : ℝ} {q : ℝ × ℝ} (hq : q ∈ Set.Icc l L ×ˢ Set.Icc m M) :
    aux_vbs_hh l L m M q ≤ q.1 * q.2 := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hq
  unfold aux_vbs_hh
  apply max_le
  · nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hy1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hy2)]

lemma aux_vbs_three {s : Set (ℝ × ℝ)} {φ : ℝ × ℝ → ℝ} (hφ : ConvexOn ℝ s φ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1)
    {P Q R : ℝ × ℝ} (hP : P ∈ s) (hQ : Q ∈ s) (hR : R ∈ s) :
    φ (a • P + b • Q + c • R) ≤ a * φ P + b * φ Q + c * φ R := by
  have := hφ.map_sum_le (t := Finset.univ) (w := ![a, b, c]) (p := ![P, Q, R])
    (by intro i _; fin_cases i <;> simp [ha, hb, hc])
    (by simp [Fin.sum_univ_three, habc])
    (by intro i _; fin_cases i <;> simp [hP, hQ, hR])
  simpa [Fin.sum_univ_three] using this

lemma aux_vbs_2d {l L m M : ℝ} {φ : ℝ × ℝ → ℝ}
    (hφ : ConvexOn ℝ (Set.Icc l L ×ˢ Set.Icc m M) φ)
    (hle : ∀ q ∈ Set.Icc l L ×ˢ Set.Icc m M, φ q ≤ q.1 * q.2)
    {p : ℝ × ℝ} (hp : p ∈ Set.Icc l L ×ˢ Set.Icc m M) :
    φ p ≤ aux_vbs_hh l L m M p := by
  have hp' := hp
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hp'
  unfold aux_vbs_hh
  rcases eq_or_lt_of_le (hx1.trans hx2) with hlL | hlL
  · have hx : p.1 = l := le_antisymm (hlL ▸ hx2) hx1
    refine le_trans (hle p hp) (le_trans (le_of_eq ?_) (le_max_left _ _))
    rw [hx]; ring
  rcases eq_or_lt_of_le (hy1.trans hy2) with hmM | hmM
  · have hy : p.2 = m := le_antisymm (hmM ▸ hy2) hy1
    refine le_trans (hle p hp) (le_trans (le_of_eq ?_) (le_max_left _ _))
    rw [hy]; ring
  have hd1 : 0 < L - l := sub_pos.2 hlL
  have hd2 : 0 < M - m := sub_pos.2 hmM
  obtain ⟨u, hu_def⟩ : ∃ u, u = (p.1 - l) / (L - l) := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v, v = (p.2 - m) / (M - m) := ⟨_, rfl⟩
  have hx : p.1 = l + u * (L - l) := by rw [hu_def, div_mul_cancel₀ _ hd1.ne']; ring
  have hy : p.2 = m + v * (M - m) := by rw [hv_def, div_mul_cancel₀ _ hd2.ne']; ring
  have hu0 : 0 ≤ u := by rw [hu_def]; exact div_nonneg (by linarith) hd1.le
  have hv0 : 0 ≤ v := by rw [hv_def]; exact div_nonneg (by linarith) hd2.le
  have hu1 : u ≤ 1 := by rw [hu_def]; exact (div_le_one hd1).2 (by linarith)
  have hv1 : v ≤ 1 := by rw [hv_def]; exact (div_le_one hd2).2 (by linarith)
  have hmemR : ∀ x y, l ≤ x → x ≤ L → m ≤ y → y ≤ M →
      ((x, y) : ℝ × ℝ) ∈ Set.Icc l L ×ˢ Set.Icc m M :=
    fun x y h1 h2 h3 h4 => ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have m1 := hmemR l m le_rfl hlL.le le_rfl hmM.le
  have m2 := hmemR L m hlL.le le_rfl le_rfl hmM.le
  have m3 := hmemR l M le_rfl hlL.le hmM.le le_rfl
  have m4 := hmemR L M hlL.le le_rfl hmM.le le_rfl
  have e1 := hle _ m1
  have e2 := hle _ m2
  have e3 := hle _ m3
  have e4 := hle _ m4
  simp only at e1 e2 e3 e4
  rcases le_total (u + v) 1 with huv | huv
  · have hpe : p = (1 - u - v) • ((l, m) : ℝ × ℝ) + u • ((L, m) : ℝ × ℝ)
        + v • ((l, M) : ℝ × ℝ) := by
      ext <;> simp [hx, hy] <;> ring
    have key := aux_vbs_three hφ (a := 1 - u - v) (b := u) (c := v) (by linarith) hu0 hv0
      (by ring) m1 m2 m3
    rw [← hpe] at key
    refine le_trans key (le_trans ?_ (le_max_left _ _))
    rw [hx, hy]
    nlinarith [mul_le_mul_of_nonneg_left e1 (by linarith : (0:ℝ) ≤ 1 - u - v),
      mul_le_mul_of_nonneg_left e2 hu0, mul_le_mul_of_nonneg_left e3 hv0]
  · have hpe : p = (u + v - 1) • ((L, M) : ℝ × ℝ) + (1 - v) • ((L, m) : ℝ × ℝ)
        + (1 - u) • ((l, M) : ℝ × ℝ) := by
      ext <;> simp [hx, hy] <;> ring
    have key := aux_vbs_three hφ (a := u + v - 1) (b := 1 - v) (c := 1 - u) (by linarith)
      (by linarith) (by linarith) (by ring) m4 m2 m3
    rw [← hpe] at key
    refine le_trans key (le_trans ?_ (le_max_right _ _))
    rw [hx, hy]
    nlinarith [mul_le_mul_of_nonneg_left e4 (by linarith : (0:ℝ) ≤ u + v - 1),
      mul_le_mul_of_nonneg_left e2 (by linarith : (0:ℝ) ≤ 1 - v),
      mul_le_mul_of_nonneg_left e3 (by linarith : (0:ℝ) ≤ 1 - u)]

lemma aux_vbs_env2d (l L m M : ℝ) (p : ℝ × ℝ) (hp : p ∈ Set.Icc l L ×ˢ Set.Icc m M) :
    convexEnvelope (Set.Icc l L ×ˢ Set.Icc m M) (fun p : ℝ × ℝ => p.1 * p.2) p
      = aux_vbs_hh l L m M p := by
  unfold convexEnvelope
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, aux_vbs_hh l L m M, aux_vbs_hh_convexOn l L m M,
        fun q hq => aux_vbs_hh_le hq, rfl⟩
    · rintro r ⟨g, hg, hgle, rfl⟩
      exact aux_vbs_2d hg hgle hp
  · apply le_csSup
    · refine ⟨p.1 * p.2, ?_⟩
      rintro r ⟨g, hg, hgle, rfl⟩
      exact hgle p hp
    · exact ⟨aux_vbs_hh l L m M, aux_vbs_hh_convexOn l L m M,
        fun q hq => aux_vbs_hh_le hq, rfl⟩

/-- Replace the `i`-th coordinate pair of `w` by `q`. -/
def aux_vbs_ins {n : ℕ} (w : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) (q : ℝ × ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (Function.update w.1 i q.1, Function.update w.2 i q.2)

lemma aux_vbs_mem_toSet {n : ℕ} (Ω : Box n) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    w ∈ Ω.toSet ↔ ∀ j, Ω.l j ≤ w.1 j ∧ w.1 j ≤ Ω.L j ∧ Ω.m j ≤ w.2 j ∧ w.2 j ≤ Ω.M j := by
  simp only [Box.toSet, Set.mem_prod, Set.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ j
    exact ⟨h1 j, h2 j, h3 j, h4 j⟩
  · intro h
    exact ⟨⟨fun j => (h j).1, fun j => (h j).2.1⟩, ⟨fun j => (h j).2.2.1, fun j => (h j).2.2.2⟩⟩

lemma aux_vbs_ins_mem {n : ℕ} (Ω : Box n) {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ Ω.toSet)
    (i : Fin n) {q : ℝ × ℝ} (hq : q ∈ Ω.rect i) : aux_vbs_ins w i q ∈ Ω.toSet := by
  rw [aux_vbs_mem_toSet] at hw ⊢
  obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩⟩ := hq
  intro j
  rcases eq_or_ne j i with rfl | hj
  · simp [aux_vbs_ins]
    exact ⟨k1, k2, k3, k4⟩
  · simpa [aux_vbs_ins, hj] using hw j

lemma aux_vbs_rect_mem {n : ℕ} (Ω : Box n) {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ Ω.toSet)
    (i : Fin n) : (w.1 i, w.2 i) ∈ Ω.rect i := by
  rw [aux_vbs_mem_toSet] at hw
  obtain ⟨h1, h2, h3, h4⟩ := hw i
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

lemma aux_vbs_ins_convex {n : ℕ} (Ω : Box n) {g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hg : ConvexOn ℝ Ω.toSet g) {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ Ω.toSet)
    (i : Fin n) (c : ℝ) :
    ConvexOn ℝ (Set.Icc (Ω.l i) (Ω.L i) ×ˢ Set.Icc (Ω.m i) (Ω.M i))
      (fun q => g (aux_vbs_ins w i q) - c) := by
  refine ⟨(convex_Icc _ _).prod (convex_Icc _ _), ?_⟩
  intro q1 hq1 q2 hq2 a b ha hb hab
  have hcomb : aux_vbs_ins w i (a • q1 + b • q2)
      = a • aux_vbs_ins w i q1 + b • aux_vbs_ins w i q2 := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      rcases eq_or_ne j i with rfl | hj
    · simp [aux_vbs_ins]
    · simp [aux_vbs_ins, hj, ← add_mul, hab]
    · simp [aux_vbs_ins]
    · simp [aux_vbs_ins, hj, ← add_mul, hab]
  have := hg.2 (aux_vbs_ins_mem Ω hw i hq1) (aux_vbs_ins_mem Ω hw i hq2) ha hb hab
  simp only [smul_eq_mul] at this ⊢
  rw [hcomb]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

/-- The partially relaxed bilinear form: envelope terms on `S`, exact products off `S`. -/
noncomputable def aux_vbs_T {n : ℕ} (Ω : Box n) (S : Finset (Fin n))
    (w : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ j, (if j ∈ S then aux_vbs_hh (Ω.l j) (Ω.L j) (Ω.m j) (Ω.M j) (w.1 j, w.2 j)
    else w.1 j * w.2 j)

lemma aux_vbs_induct {n : ℕ} (Ω : Box n) {g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hg : ConvexOn ℝ Ω.toSet g) (hgle : ∀ w ∈ Ω.toSet, g w ≤ bilin w)
    (S : Finset (Fin n)) : ∀ w ∈ Ω.toSet, g w ≤ aux_vbs_T Ω S w := by
  induction S using Finset.induction_on with
  | empty => intro w hw; simpa [aux_vbs_T, bilin] using hgle w hw
  | insert i S hi ih =>
    intro w hw
    set c := ∑ j ∈ Finset.univ.erase i,
      (if j ∈ S then aux_vbs_hh (Ω.l j) (Ω.L j) (Ω.m j) (Ω.M j) (w.1 j, w.2 j)
        else w.1 j * w.2 j) with hc
    have hφ := aux_vbs_ins_convex Ω hg hw i c
    have hle : ∀ q ∈ Set.Icc (Ω.l i) (Ω.L i) ×ˢ Set.Icc (Ω.m i) (Ω.M i),
        g (aux_vbs_ins w i q) - c ≤ q.1 * q.2 := by
      intro q hq
      have h := ih _ (aux_vbs_ins_mem Ω hw i hq)
      unfold aux_vbs_T at h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
      have hsum : ∑ j ∈ Finset.univ.erase i,
          (if j ∈ S then aux_vbs_hh (Ω.l j) (Ω.L j) (Ω.m j) (Ω.M j)
            ((aux_vbs_ins w i q).1 j, (aux_vbs_ins w i q).2 j)
          else (aux_vbs_ins w i q).1 j * (aux_vbs_ins w i q).2 j) = c := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp [aux_vbs_ins, hji]
      rw [hsum, if_neg hi] at h
      have hq12 : (aux_vbs_ins w i q).1 i * (aux_vbs_ins w i q).2 i = q.1 * q.2 := by
        simp [aux_vbs_ins]
      rw [hq12] at h
      linarith
    have key := aux_vbs_2d hφ hle (aux_vbs_rect_mem Ω hw i)
    have hins : aux_vbs_ins w i (w.1 i, w.2 i) = w := by simp [aux_vbs_ins]
    simp only [hins] at key
    unfold aux_vbs_T
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hsum : ∑ j ∈ Finset.univ.erase i,
        (if j ∈ insert i S then aux_vbs_hh (Ω.l j) (Ω.L j) (Ω.m j) (Ω.M j) (w.1 j, w.2 j)
          else w.1 j * w.2 j) = c := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [Finset.mem_insert, hji]
    rw [hsum]
    simp only [Finset.mem_insert, true_or, if_true]
    linarith

/-- The separable candidate envelope. -/
noncomputable def aux_vbs_H {n : ℕ} (Ω : Box n) (w : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, aux_vbs_hh (Ω.l i) (Ω.L i) (Ω.m i) (Ω.M i) (w.1 i, w.2 i)

lemma aux_vbs_H_convexOn {n : ℕ} (Ω : Box n) : ConvexOn ℝ Ω.toSet (aux_vbs_H Ω) := by
  refine ⟨?_, ?_⟩
  · exact ((convex_Icc _ _).prod (convex_Icc _ _))
  · intro w1 _ w2 _ a b ha hb hab
    unfold aux_vbs_H
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have := aux_vbs_hh_comb (Ω.l i) (Ω.L i) (Ω.m i) (Ω.M i) (w1.1 i, w1.2 i) (w2.1 i, w2.2 i)
      a b ha hb hab
    have e : ((a • w1 + b • w2).1 i, (a • w1 + b • w2).2 i)
        = a • (w1.1 i, w1.2 i) + b • (w2.1 i, w2.2 i) := by
      ext <;> simp
    rw [e]
    exact this

lemma aux_vbs_H_le {n : ℕ} (Ω : Box n) {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ Ω.toSet) :
    aux_vbs_H Ω w ≤ bilin w := by
  unfold aux_vbs_H bilin
  apply Finset.sum_le_sum
  intro i _
  exact aux_vbs_hh_le (aux_vbs_rect_mem Ω hw i)

lemma aux_vbs_envn {n : ℕ} (Ω : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ Ω.toSet) :
    convexEnvelope Ω.toSet bilin z = aux_vbs_H Ω z := by
  unfold convexEnvelope
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, aux_vbs_H Ω, aux_vbs_H_convexOn Ω, fun w hw => aux_vbs_H_le Ω hw, rfl⟩
    · rintro r ⟨g, hg, hgle, rfl⟩
      have h := aux_vbs_induct Ω hg hgle Finset.univ z hz
      simpa [aux_vbs_T, aux_vbs_H] using h
  · apply le_csSup
    · refine ⟨bilin z, ?_⟩
      rintro r ⟨g, hg, hgle, rfl⟩
      exact hgle z hz
    · exact ⟨aux_vbs_H Ω, aux_vbs_H_convexOn Ω, fun w hw => aux_vbs_H_le Ω hw, rfl⟩

end BiconvexProg.BranchBound

open BiconvexProg.BranchBound

theorem solution {n : ℕ} (Ω : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hz : z ∈ Ω.toSet) :
    convexEnvelope Ω.toSet bilin z =
      ∑ i, convexEnvelope (Ω.rect i) (fun p : ℝ × ℝ => p.1 * p.2) (z.1 i, z.2 i) := by
  rw [aux_vbs_envn Ω z hz]
  unfold aux_vbs_H
  apply Finset.sum_congr rfl
  intro i _
  exact (aux_vbs_env2d _ _ _ _ _ (aux_vbs_rect_mem Ω hz i)).symm
