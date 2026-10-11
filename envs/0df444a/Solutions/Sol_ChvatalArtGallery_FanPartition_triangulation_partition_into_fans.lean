-- Prove2me | solution 1 for ChvatalArtGallery.FanPartition.triangulation_partition_into_fans
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T05:46:29.536862+00:00
-- url     : https://prove2.me/submissions/3d0e6177-d2b4-49b6-8960-0011aef40192

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

-- BEGIN COMPLETE MODULE ChordOrder
section

namespace ChvatalArtGallery.FanPartition.Proof
variable {n : ℕ}

lemma cdist_formula (a b : Fin n) :
    cdist a b = if a.val ≤ b.val then b.val-a.val else b.val+n-a.val := by
  unfold cdist
  split_ifs with h
  · have he : b.val+n-a.val = n+(b.val-a.val) := by omega
    rw [he,Nat.add_mod]
    simp only [Nat.mod_self,zero_add]
    have hh : b.val-a.val < n := by omega
    simp [Nat.mod_eq_of_lt hh]
  · exact Nat.mod_eq_of_lt (by omega)

lemma boundary_mk_iff (hn : 3 ≤ n) (a b : Fin n) :
    IsBoundaryEdge s(a,b) ↔ a.val+1=b.val ∨ b.val+1=a.val ∨
      (a.val=0 ∧ b.val+1=n) ∨ (b.val=0 ∧ a.val+1=n) := by
  constructor
  · rintro ⟨u,v,h,hc⟩
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rw [cdist_formula] at hc <;> split_ifs at hc <;> omega
  · intro h
    by_cases hab : a.val ≤ b.val
    · rcases h with h | h | h | h
      · exact ⟨a,b,rfl,by rw [cdist_formula,if_pos hab]; omega⟩
      · omega
      · refine ⟨b,a,Sym2.eq_swap,?_⟩
        rw [cdist_formula,if_neg (by omega)]
        omega
      · omega
    · rcases h with h | h | h | h
      · omega
      · exact ⟨b,a,Sym2.eq_swap,by rw [cdist_formula,if_pos (by omega)]; omega⟩
      · omega
      · refine ⟨a,b,rfl,?_⟩
        rw [cdist_formula,if_neg hab]
        omega

lemma diagonal_mk_iff (a b : Fin n) :
    IsDiagonal s(a,b) ↔ a ≠ b ∧ cdist a b ≠ 1 ∧ cdist b a ≠ 1 := by
  constructor
  · exact fun h => h a b rfl
  · rintro ⟨hne,hab,hba⟩ u v he
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hne,hab,hba⟩
    · exact ⟨hne.symm,hba,hab⟩

lemma diagonal_sorted_iff (hn : 3 ≤ n) (a b : Fin n) (hab : a.val < b.val) :
    IsDiagonal s(a,b) ↔ a.val+1 < b.val ∧ ¬ (a.val=0 ∧ b.val+1=n) := by
  rw [diagonal_mk_iff,cdist_formula,cdist_formula,if_pos (by omega),if_neg (by omega)]
  constructor
  · rintro ⟨_,h1,h2⟩; omega
  · intro h; refine ⟨by intro he; cases he; omega,?_,?_⟩ <;> omega

lemma oriented_cross_formula (a b c d : Fin n) :
    (0 < cdist a c ∧ cdist a c < cdist a b ∧ cdist a b < cdist a d) ↔
      (a.val<c.val ∧ c.val<b.val ∧ (b.val<d.val ∨ d.val<a.val)) ∨
      (b.val<a.val ∧ (a.val<c.val ∨ c.val<b.val) ∧ b.val<d.val ∧ d.val<a.val) := by
  simp only [cdist_formula]
  split_ifs <;> omega

lemma crosses_sorted_iff (a b c d : Fin n) (hab : a.val < b.val) (hcd : c.val < d.val) :
    Crosses s(a,b) s(c,d) ↔
      (a.val<c.val ∧ c.val<b.val ∧ b.val<d.val) ∨
      (c.val<a.val ∧ a.val<d.val ∧ d.val<b.val) := by
  constructor
  · rintro ⟨u,v,w,z,he,hf,hx⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases Sym2.eq_iff.mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rw [oriented_cross_formula] at hx <;> omega
  · rintro (h | h)
    · exact ⟨a,b,c,d,rfl,rfl,(oriented_cross_formula a b c d).mpr (Or.inl ⟨h.1,h.2.1,Or.inl h.2.2⟩)⟩
    · refine ⟨a,b,d,c,rfl,Sym2.eq_swap,?_⟩
      apply (oriented_cross_formula a b d c).mpr
      exact Or.inl ⟨h.2.1,h.2.2,Or.inr h.1⟩

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE ChordOrder

-- BEGIN COMPLETE MODULE OrderedEar
section

namespace ChvatalArtGallery.FanPartition.Proof

/-- A shortest non-boundary edge forces an ear chord in a maximal noncrossing set. -/
theorem ordered_ear_exists {n : ℕ} (hn : 4 ≤ n) (R : Fin n → Fin n → Prop)
    (hne : ∃ a b, a < b ∧ R a b)
    (hdiag : ∀ a b, a < b → R a b → a.val + 1 < b.val)
    (hnc : ∀ a b c d, a < b → c < d → R a b → R c d →
      ¬ ((a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)))
    (hmax : ∀ a b, a.val + 1 < b.val → ¬ (a.val = 0 ∧ b.val + 1 = n) →
      (∀ c d, c < d → R c d →
        ¬ ((a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b))) → R a b) :
    ∃ a b, R a b ∧ b.val = a.val + 2 := by
  classical
  have hex : ∃ k, ∃ a b : Fin n, a < b ∧ R a b ∧ b.val - a.val = k := by
    obtain ⟨a, b, hab, hR⟩ := hne
    exact ⟨_, a, b, hab, hR, rfl⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hmin : ∀ j, (∃ a b : Fin n, a < b ∧ R a b ∧ b.val - a.val = j) → k ≤ j :=
    fun j hj => Nat.find_min' hex hj
  obtain ⟨a, b, hab, hR, hk⟩ := hk
  have hgap := hdiag a b hab hR
  have htwo : a.val + 2 < n := by omega
  let z : Fin n := ⟨a.val + 2, htwo⟩
  have haz : a.val + 1 < z.val := by dsimp [z]; omega
  have hbd : ¬ (a.val = 0 ∧ z.val + 1 = n) := by
    dsimp [z]
    omega
  have hz : R a z := hmax a z haz hbd (by
    intro c d hcd hcdR hcross
    rcases hcross with ⟨hac, hcz, hzd⟩ | ⟨hca, had, hdz⟩
    · have hc : c.val = a.val + 1 := by have hzval : z.val = a.val + 2 := rfl; simp only [Fin.lt_def] at hac hcz; omega
      by_cases hdb : d ≤ b
      · have hshort := hmin (d.val - c.val) ⟨c, d, hcd, hcdR, rfl⟩
        change d.val ≤ b.val at hdb
        omega
      · have hbd' : b < d := lt_of_not_ge hdb
        exact hnc a b c d hab hcd hR hcdR (Or.inl ⟨hac, by change c.val < b.val; omega, hbd'⟩)
    · have hd : d.val = a.val + 1 := by have hzval : z.val = a.val + 2 := rfl; simp only [Fin.lt_def] at had hdz; omega
      exact hnc a b c d hab hcd hR hcdR (Or.inr ⟨hca, had, by change d.val < b.val; omega⟩))
  exact ⟨a, z, hz, rfl⟩

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE OrderedEar

-- BEGIN COMPLETE MODULE NativeEar
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma diagonal_ordered_endpoints {n : ℕ} (e : Sym2 (Fin n)) (he : IsDiagonal e) :
    ∃ a b : Fin n, a < b ∧ e = s(a,b) := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hne := (diagonal_mk_iff a b).mp he |>.1
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a,b,h,rfl⟩
    · exact ⟨b,a,h,Sym2.eq_swap⟩

lemma triangulation_diagonals_nonempty {n : ℕ} (hn : 4 ≤ n)
    {D : Finset (Sym2 (Fin n))} (hD : IsTriangulation n D) : D.Nonempty := by
  by_contra h
  have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨2,by omega⟩
  have hd : IsDiagonal s(a,b) := (diagonal_sorted_iff (by omega) a b (by change 0 < 2; omega)).mpr (by
    dsimp [a,b]; omega)
  have hm := hD.2.2.2 s(a,b) hd (by simp [he])
  simp [he] at hm

lemma triangulation_ear_chord {n : ℕ} (hn : 4 ≤ n)
    {D : Finset (Sym2 (Fin n))} (hD : IsTriangulation n D) :
    ∃ a b : Fin n, s(a,b) ∈ D ∧ b.val = a.val + 2 := by
  apply ordered_ear_exists hn (fun a b => s(a,b) ∈ D)
  · obtain ⟨e,he⟩ := triangulation_diagonals_nonempty hn hD
    obtain ⟨a,b,hab,rfl⟩ := diagonal_ordered_endpoints e (hD.2.1 e he)
    exact ⟨a,b,hab,he⟩
  · intro a b hab he
    exact ((diagonal_sorted_iff hD.1 a b hab).mp (hD.2.1 _ he)).1
  · intro a b c d hab hcd he hf hx
    exact hD.2.2.1 _ he _ hf ((crosses_sorted_iff a b c d hab hcd).mpr hx)
  · intro a b hab hwrap hnc
    apply hD.2.2.2 _ ((diagonal_sorted_iff hD.1 a b (by omega)).mpr ⟨hab,hwrap⟩)
    intro e he hx
    obtain ⟨c,d,hcd,rfl⟩ := diagonal_ordered_endpoints e (hD.2.1 e he)
    exact hnc c d hcd he ((crosses_sorted_iff a b c d (by omega) hcd).mp hx)

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE NativeEar

-- BEGIN COMPLETE MODULE EarNeighbours
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma ear_only_neighbours {n : ℕ} {D : Finset (Sym2 (Fin n))}
    (hD : IsTriangulation n D) (a b v : Fin n) (he : s(a,b) ∈ D)
    (hb : b.val = a.val + 2) (hv : v.val = a.val + 1) (w : Fin n)
    (hw : IsEdge D s(v,w)) : w = a ∨ w = b := by
  by_contra h
  have hwa : w ≠ a := fun e => h (Or.inl e)
  have hwb : w ≠ b := fun e => h (Or.inr e)
  have hva : w.val ≠ a.val := fun e => hwa (Fin.ext e)
  have hvb : w.val ≠ b.val := fun e => hwb (Fin.ext e)
  rcases hw with hw | hw
  · have hboundary := (boundary_mk_iff hD.1 v w).mp hw
    omega
  · have hd := hD.2.1 _ hw
    have hne := ((diagonal_mk_iff v w).mp hd).1
    have hval : w.val ≠ v.val := fun e => hne (Fin.ext e.symm)
    have hcross : Crosses s(a,b) s(v,w) := by
      by_cases hvw : v.val < w.val
      · apply (crosses_sorted_iff a b v w (by omega) hvw).mpr
        left; omega
      · rw [show s(v,w) = s(w,v) from Sym2.eq_swap]
        apply (crosses_sorted_iff a b w v (by omega) (by omega)).mpr
        right; omega
    exact hD.2.2.1 _ he _ hw hcross

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarNeighbours

-- BEGIN COMPLETE MODULE DeletionOrder
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma succAbove_value {n : ℕ} (v : Fin (n+1)) (i : Fin n) :
    (v.succAbove i).val = if i.val < v.val then i.val else i.val+1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

lemma crosses_strictMono {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (a b c d : Fin m) (hab : a.val < b.val) (hcd : c.val < d.val) :
    Crosses s(f a,f b) s(f c,f d) ↔ Crosses s(a,b) s(c,d) := by
  rw [crosses_sorted_iff _ _ _ _ (hf hab) (hf hcd), crosses_sorted_iff _ _ _ _ hab hcd]
  simp only [← Fin.lt_def, hf.lt_iff_lt]

lemma succAbove_diagonal {n : ℕ} (hn : 3 ≤ n) (v : Fin (n+1))
    (_hv0 : 0 < v.val) (_hvn : v.val < n) (a b : Fin n) (hab : a.val < b.val)
    (hd : IsDiagonal s(a,b)) : IsDiagonal s(v.succAbove a,v.succAbove b) := by
  have ha := succAbove_value v a
  have hb := succAbove_value v b
  have h := (diagonal_sorted_iff hn a b hab).mp hd
  apply (diagonal_sorted_iff (by omega) _ _ (Fin.strictMono_succAbove v hab)).mpr
  split_ifs at ha hb <;> omega

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE DeletionOrder

-- BEGIN COMPLETE MODULE DeletionFacts
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma diagonal_not_boundary {n : ℕ} {e : Sym2 (Fin n)} (h : IsDiagonal e) :
    ¬ IsBoundaryEdge e := by
  rintro ⟨a,b,he,hab⟩
  exact (h a b he).2.1 hab

lemma crossing_sorted_diagonal_right {n : ℕ} (hn : 3 ≤ n)
    (a b c d : Fin n) (hab : a.val < b.val) (hcd : c.val < d.val)
    (hx : Crosses s(a,b) s(c,d)) : IsDiagonal s(c,d) := by
  have h := (crosses_sorted_iff a b c d hab hcd).mp hx
  apply (diagonal_sorted_iff hn c d hcd).mpr
  omega

lemma ear_no_diagonal_tip {n : ℕ} {D : Finset (Sym2 (Fin n))}
    (hD : IsTriangulation n D) (a b v : Fin n) (he : s(a,b) ∈ D)
    (hb : b.val = a.val + 2) (hv : v.val = a.val + 1) (w : Fin n) :
    s(v,w) ∉ D := by
  intro hw
  have hnb := diagonal_not_boundary (hD.2.1 _ hw)
  apply hnb
  apply (boundary_mk_iff hD.1 v w).mpr
  rcases ear_only_neighbours hD a b v he hb hv w (Or.inr hw) with rfl | rfl <;> omega

lemma ear_diagonal_avoids {n : ℕ} {D : Finset (Sym2 (Fin n))}
    (hD : IsTriangulation n D) (a b v : Fin n) (he : s(a,b) ∈ D)
    (hb : b.val = a.val + 2) (hv : v.val = a.val + 1)
    (c d : Fin n) (hcd : s(c,d) ∈ D) : c ≠ v ∧ d ≠ v := by
  constructor
  · intro h; subst c
    exact ear_no_diagonal_tip hD a b v he hb hv d hcd
  · intro h; subst d
    exact ear_no_diagonal_tip hD a b v he hb hv c (by simpa only [Sym2.eq_swap] using hcd)

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE DeletionFacts

-- BEGIN COMPLETE MODULE EarDeletion
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma mem_pullback_iff {m n : ℕ} (f : Fin m → Fin n)
    (D : Finset (Sym2 (Fin n))) (e : Sym2 (Fin m)) :
    e ∈ pullback f D ↔ IsDiagonal e ∧ Sym2.map f e ∈ D := by
  simp [pullback]

lemma ear_delete_triangulation {n : ℕ} (hn : 3 ≤ n)
    {D : Finset (Sym2 (Fin (n+1)))} (hD : IsTriangulation (n+1) D)
    (a b v : Fin (n+1)) (he : s(a,b) ∈ D)
    (hb : b.val = a.val + 2) (hv : v.val = a.val + 1)
    (hv0 : 0 < v.val) (hvn : v.val < n) :
    IsTriangulation n (pullback v.succAbove D) := by
  classical
  refine ⟨hn,?_,?_,?_⟩
  · intro e he
    exact ((mem_pullback_iff _ _ _).mp he).1
  · intro e he f hf hx
    have he' := (mem_pullback_iff _ _ _).mp he
    have hf' := (mem_pullback_iff _ _ _).mp hf
    obtain ⟨c,d,hcd,rfl⟩ := diagonal_ordered_endpoints e he'.1
    obtain ⟨s,t,hst,rfl⟩ := diagonal_ordered_endpoints f hf'.1
    exact hD.2.2.1 _ he'.2 _ hf'.2
      ((crosses_strictMono v.succAbove (Fin.strictMono_succAbove v) c d s t hcd hst).mpr hx)
  · intro e hd hnc
    obtain ⟨c,d,hcd,rfl⟩ := diagonal_ordered_endpoints e hd
    apply (mem_pullback_iff _ _ _).mpr
    refine ⟨hd,?_⟩
    apply hD.2.2.2 _ (succAbove_diagonal hn v hv0 hvn c d hcd hd)
    intro f hf hx
    obtain ⟨s,t,hst,rfl⟩ := diagonal_ordered_endpoints f (hD.2.1 _ hf)
    obtain ⟨hsv,htv⟩ := ear_diagonal_avoids hD a b v he hb hv s t hf
    obtain ⟨s',rfl⟩ := Fin.exists_succAbove_eq hsv
    obtain ⟨t',rfl⟩ := Fin.exists_succAbove_eq htv
    have hst' : s' < t' := (Fin.strictMono_succAbove v).lt_iff_lt.mp hst
    have hx' := (crosses_strictMono v.succAbove (Fin.strictMono_succAbove v) c d s' t' hcd hst').mp hx
    have hdi := crossing_sorted_diagonal_right hn c d s' t' hcd hst' hx'
    exact hnc s(s',t') ((mem_pullback_iff _ _ _).mpr ⟨hdi,hf⟩) hx'

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarDeletion

-- BEGIN COMPLETE MODULE EarEdgeTransport
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma non_diagonal_boundary {n : ℕ} (hn : 3 ≤ n) (a b : Fin n)
    (hne : a ≠ b) (hd : ¬ IsDiagonal s(a,b)) : IsBoundaryEdge s(a,b) := by
  apply (boundary_mk_iff hn a b).mpr
  rcases lt_or_gt_of_ne hne with h | h
  · have h' := mt (diagonal_sorted_iff hn a b h).mpr hd
    omega
  · have hd' : ¬ IsDiagonal s(b,a) := by simpa only [Sym2.eq_swap] using hd
    have h' := mt (diagonal_sorted_iff hn b a h).mpr hd'
    omega

lemma succAbove_boundary_forward {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n+1)) (hv0 : 0 < v.val) (hvn : v.val < n) (a b : Fin n) (h : IsBoundaryEdge s(a,b)) :
    IsBoundaryEdge s(v.succAbove a,v.succAbove b) ∨
      ((v.succAbove a).val+1=v.val ∧ v.val+1=(v.succAbove b).val) ∨
      ((v.succAbove b).val+1=v.val ∧ v.val+1=(v.succAbove a).val) := by
  have ha := succAbove_value v a
  have hb := succAbove_value v b
  have h' := (boundary_mk_iff hn a b).mp h
  rw [boundary_mk_iff (by omega)]
  split_ifs at ha hb <;> omega

lemma succAbove_boundary_backward {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n+1)) (a b : Fin n)
    (h : IsBoundaryEdge s(v.succAbove a,v.succAbove b)) : IsBoundaryEdge s(a,b) := by
  have ha := succAbove_value v a
  have hb := succAbove_value v b
  have h' := (boundary_mk_iff (by omega) _ _).mp h
  apply (boundary_mk_iff hn a b).mpr
  split_ifs at ha hb <;> omega

lemma ear_delete_edge_iff {n : ℕ} (hn : 3 ≤ n)
    {D : Finset (Sym2 (Fin (n+1)))} (hD : IsTriangulation (n+1) D)
    (a b v : Fin (n+1)) (he : s(a,b) ∈ D)
    (hb : b.val = a.val + 2) (hv : v.val = a.val + 1)
    (hv0 : 0 < v.val) (hvn : v.val < n) (c d : Fin n) :
    IsEdge (pullback v.succAbove D) s(c,d) ↔ IsEdge D s(v.succAbove c,v.succAbove d) := by
  constructor
  · rintro (h | h)
    · rcases succAbove_boundary_forward hn v hv0 hvn c d h with h | h | h
      · exact Or.inl h
      · have hc : v.succAbove c = a := Fin.ext (by omega)
        have hd : v.succAbove d = b := Fin.ext (by omega)
        exact Or.inr (by simpa only [hc,hd] using he)
      · have hc : v.succAbove c = b := Fin.ext (by omega)
        have hd : v.succAbove d = a := Fin.ext (by omega)
        exact Or.inr (by simpa only [hc,hd,Sym2.eq_swap] using he)
    · exact Or.inr ((mem_pullback_iff _ _ _).mp h).2
  · rintro (h | h)
    · exact Or.inl (succAbove_boundary_backward hn v c d h)
    · by_cases hd : IsDiagonal s(c,d)
      · exact Or.inr ((mem_pullback_iff _ _ _).mpr ⟨hd,h⟩)
      · apply Or.inl
        apply non_diagonal_boundary hn c d _ hd
        intro heq
        have hne := ((diagonal_mk_iff _ _).mp (hD.2.1 _ h)).1
        exact hne (congrArg v.succAbove heq)

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarEdgeTransport

-- BEGIN COMPLETE MODULE DeletionInterface
section

namespace ChvatalArtGallery.FanPartition.Proof

/-- Delete an actual interior ear, retaining the native maximal triangulation and all edges. -/
theorem exists_deleted_triangulation {n : ℕ} (hn : 3 ≤ n)
    {D : Finset (Sym2 (Fin (n+1)))} (hD : IsTriangulation (n+1) D) :
    ∃ v : Fin (n+1), 0 < v.val ∧ v.val < n ∧
      IsTriangulation n (pullback v.succAbove D) ∧
      (∀ c d : Fin n, IsEdge (pullback v.succAbove D) s(c,d) ↔
        IsEdge D s(v.succAbove c,v.succAbove d)) ∧
      (∀ w : Fin (n+1), IsEdge D s(v,w) ↔
        w.val+1=v.val ∨ v.val+1=w.val) := by
  obtain ⟨a,b,he,hb⟩ := triangulation_ear_chord (by omega) hD
  let v : Fin (n+1) := ⟨a.val+1,by omega⟩
  have hv : v.val = a.val+1 := rfl
  have hv0 : 0 < v.val := by omega
  have hvn : v.val < n := by omega
  refine ⟨v,hv0,hvn,ear_delete_triangulation hn hD a b v he hb hv hv0 hvn,
    ear_delete_edge_iff hn hD a b v he hb hv hv0 hvn,?_⟩
  intro w
  constructor
  · intro hw
    rcases ear_only_neighbours hD a b v he hb hv w hw with rfl | rfl <;> omega
  · intro hw
    apply Or.inl
    apply (boundary_mk_iff hD.1 v w).mpr
    omega

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE DeletionInterface

-- BEGIN COMPLETE MODULE TriangleMaps
section

namespace ChvatalArtGallery.FanPartition.Proof
variable {m n : ℕ}

def faceEmbedding (e : Fin m ↪ Fin n) : Finset (Fin m) ↪ Finset (Fin n) :=
  ⟨Finset.map e, Finset.map_injective e⟩

def mapFaces (e : Fin m ↪ Fin n) (F : Finset (Finset (Fin m))) : Finset (Finset (Fin n)) :=
  F.map (faceEmbedding e)

lemma adjacent_symm {T U : Finset (Fin n)} (h : Adjacent T U) : Adjacent U T := by
  exact ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩

lemma adjacent_map_iff (e : Fin m ↪ Fin n) (T U : Finset (Fin m)) :
    Adjacent (T.map e) (U.map e) ↔ Adjacent T U := by
  simp only [Adjacent,ne_eq,Finset.map_inj,← Finset.map_inter,Finset.card_map]

lemma dualConnected_singleton (T : Finset (Fin n)) : DualConnected {T} := by
  intro S hS hn _
  obtain ⟨U,hU⟩ := hn
  have he : U=T := Finset.mem_singleton.mp (hS hU)
  apply Finset.Subset.antisymm hS
  intro V hV
  simpa only [Finset.mem_singleton.mp hV,← he] using hU

lemma dualConnected_map (e : Fin m ↪ Fin n) {F : Finset (Finset (Fin m))}
    (hF : DualConnected F) : DualConnected (mapFaces e F) := by
  intro S hS hn hc
  let T := F.filter (fun A => A.map e ∈ S)
  have hT : T = F := by
    apply hF T (Finset.filter_subset _ _)
    · obtain ⟨A,hA⟩ := hn
      obtain ⟨B,hB,rfl⟩ := Finset.mem_map.mp (hS hA)
      exact ⟨B,Finset.mem_filter.mpr ⟨hB,hA⟩⟩
    · intro A hA B hB hab
      refine Finset.mem_filter.mpr ⟨hB,?_⟩
      exact hc (A.map e) (Finset.mem_filter.mp hA).2 (B.map e)
        (Finset.mem_map.mpr ⟨B,hB,rfl⟩) ((adjacent_map_iff e A B).mpr hab)
  apply Finset.Subset.antisymm hS
  intro A hA
  obtain ⟨B,hB,rfl⟩ := Finset.mem_map.mp hA
  have hb : B ∈ T := hT ▸ hB
  exact (Finset.mem_filter.mp hb).2

lemma dualConnected_insert {F : Finset (Finset (Fin n))} (hF : DualConnected F)
    {E T : Finset (Fin n)} (hT : T ∈ F) (hTE : Adjacent T E) :
    DualConnected (insert E F) := by
  intro S hS hn hc
  have hnon : (S ∩ F).Nonempty := by
    obtain ⟨A,hA⟩ := hn
    rcases Finset.mem_insert.mp (hS hA) with he | hAF
    · subst A
      exact ⟨T,Finset.mem_inter.mpr ⟨hc E hA T (Finset.mem_insert_of_mem hT)
        (adjacent_symm hTE),hT⟩⟩
    · exact ⟨A,Finset.mem_inter.mpr ⟨hA,hAF⟩⟩
  have heq : S ∩ F = F := hF _ Finset.inter_subset_right hnon (by
    intro A hA B hB hab
    exact Finset.mem_inter.mpr ⟨hc A (Finset.mem_inter.mp hA).1 B
      (Finset.mem_insert_of_mem hB) hab,hB⟩)
  have hFS : F ⊆ S := by
    intro A hA
    have : A ∈ S ∩ F := by rw [heq]; exact hA
    exact (Finset.mem_inter.mp this).1
  apply Finset.Subset.antisymm hS
  intro A hA
  rcases Finset.mem_insert.mp hA with he | hAF
  · subst A
    exact hc T (hFS hT) E (Finset.mem_insert_self _ _) hTE
  · exact hFS hAF

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE TriangleMaps

-- BEGIN COMPLETE MODULE TriangleBasics
section

namespace ChvatalArtGallery.FanPartition.Proof
variable {n : ℕ} {D : Finset (Sym2 (Fin n))}

lemma mem_triangles_iff {T : Finset (Fin n)} : T ∈ triangles n D ↔
    T.card = 3 ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → IsEdge D s(a,b) := by
  simp [triangles,Finset.mem_powersetCard]

def vertexStar (D : Finset (Sym2 (Fin n))) (v : Fin n) : Finset (Finset (Fin n)) :=
  (triangles n D).filter (fun T => v ∈ T)

lemma mem_vertexStar {v : Fin n} {T : Finset (Fin n)} :
    T ∈ vertexStar D v ↔ T ∈ triangles n D ∧ v ∈ T := by
  simp [vertexStar]

lemma vertexStar_fan {v : Fin n} (hn : (vertexStar D v).Nonempty)
    (hc : DualConnected (vertexStar D v)) : IsFan n D (vertexStar D v) := by
  refine ⟨Finset.filter_subset _ _,hn,hc,v,?_⟩
  intro T hT U hU _
  exact Finset.mem_inter.mpr ⟨(mem_vertexStar.mp hT).2,(mem_vertexStar.mp hU).2⟩

def ProperColour (D : Finset (Sym2 (Fin n))) (c : Fin n → Fin 3) : Prop :=
  ∀ a b, a ≠ b → IsEdge D s(a,b) → c a ≠ c b

lemma triangle_colour_bijective {c : Fin n → Fin 3} (hc : ProperColour D c)
    {T : Finset (Fin n)} (hT : T ∈ triangles n D) :
    Function.Bijective (fun a : T => c a) := by
  have hinj : Function.Injective (fun a : T => c a) := by
    intro a b he
    apply Subtype.ext
    by_contra hab
    exact hc a b hab ((mem_triangles_iff.mp hT).2 a a.property b b.property hab) he
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨hinj,by simpa using (mem_triangles_iff.mp hT).1⟩

lemma triangle_colour_exists {c : Fin n → Fin 3} (hc : ProperColour D c)
    {T : Finset (Fin n)} (hT : T ∈ triangles n D) (k : Fin 3) :
    ∃ v ∈ T, c v = k := by
  obtain ⟨v,hv⟩ := (triangle_colour_bijective hc hT).2 k
  exact ⟨v,v.property,hv⟩

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE TriangleBasics

-- BEGIN COMPLETE MODULE TriangleDeletion
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma triangle_map_iff {m n : ℕ} (e : Fin m ↪ Fin n)
    (D : Finset (Sym2 (Fin n))) (C : Finset (Sym2 (Fin m)))
    (he : ∀ a b, IsEdge C s(a,b) ↔ IsEdge D s(e a,e b)) (T : Finset (Fin m)) :
    T.map e ∈ triangles n D ↔ T ∈ triangles m C := by
  rw [mem_triangles_iff,mem_triangles_iff,Finset.card_map]
  constructor
  · rintro ⟨hc,hT⟩
    refine ⟨hc,?_⟩
    intro a ha b hb hab
    exact (he a b).mpr (hT (e a) (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
      (e b) (Finset.mem_map.mpr ⟨b,hb,rfl⟩) (e.injective.ne hab))
  · rintro ⟨hc,hT⟩
    refine ⟨hc,?_⟩
    intro a ha b hb hab
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
    exact (he x y).mp (hT x hx y hy (by intro h; exact hab (congrArg e h)))

lemma triangles_delete_eq {n : ℕ} (v : Fin (n+1)) (e : Fin n ↪ Fin (n+1))
    (herange : ∀ w, w ≠ v → ∃ i, e i = w) (heavoid : ∀ i, e i ≠ v)
    (D : Finset (Sym2 (Fin (n+1)))) (C : Finset (Sym2 (Fin n)))
    (hedge : ∀ a b, IsEdge C s(a,b) ↔ IsEdge D s(e a,e b))
    (l r : Fin n) (hlr : l ≠ r)
    (hnb : ∀ w, IsEdge D s(v,w) ↔ w = e l ∨ w = e r)
    (hbase : IsEdge C s(l,r)) :
    triangles (n+1) D = insert {v,e l,e r} (mapFaces e (triangles n C)) := by
  classical
  have hvl : v ≠ e l := (heavoid l).symm
  have hvr : v ≠ e r := (heavoid r).symm
  have helr : e l ≠ e r := e.injective.ne hlr
  have hcard : ({v,e l,e r} : Finset (Fin (n+1))).card = 3 := by simp [hvl,hvr,helr]
  have hear : ({v,e l,e r} : Finset (Fin (n+1))) ∈ triangles (n+1) D := by
    apply mem_triangles_iff.mpr
    refine ⟨hcard,?_⟩
    intro a ha b hb hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact (hnb _).mpr (Or.inl rfl)
    · exact (hnb _).mpr (Or.inr rfl)
    · simpa only [Sym2.eq_swap] using (hnb _).mpr (Or.inl rfl)
    · exact (hab rfl).elim
    · exact (hedge _ _).mp hbase
    · simpa only [Sym2.eq_swap] using (hnb _).mpr (Or.inr rfl)
    · simpa only [Sym2.eq_swap] using (hedge _ _).mp hbase
    · exact (hab rfl).elim
  ext T
  constructor
  · intro hT
    by_cases hvT : v ∈ T
    · apply Finset.mem_insert.mpr
      left
      apply Finset.eq_of_subset_of_card_le _ (by rw [hcard,(mem_triangles_iff.mp hT).1])
      intro w hw
      by_cases hwv : w = v
      · simp [hwv]
      · have h := (hnb w).mp ((mem_triangles_iff.mp hT).2 v hvT w hw (Ne.symm hwv))
        simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inr h
    · let U : Finset (Fin n) := Finset.univ.filter (fun i => e i ∈ T)
      have hmap : U.map e = T := by
        ext w
        constructor
        · intro hw
          obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hw
          exact (Finset.mem_filter.mp hi).2
        · intro hw
          obtain ⟨i,rfl⟩ := herange w (by intro h; exact hvT (h ▸ hw))
          exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩
      apply Finset.mem_insert_of_mem
      apply Finset.mem_map.mpr
      refine ⟨U,?_,hmap⟩
      apply (triangle_map_iff e D C hedge U).mp
      rwa [hmap]
  · intro hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact hear
    · obtain ⟨U,hU,rfl⟩ := Finset.mem_map.mp hT
      exact (triangle_map_iff e D C hedge U).mpr hU

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE TriangleDeletion

-- BEGIN COMPLETE MODULE EarReduction
section

namespace ChvatalArtGallery.FanPartition.Proof

/-- Complete finite ear reduction, including exact native triangles and neighbour incidence. -/
theorem ear_reduction {n : ℕ} (hn : 3 ≤ n)
    {D : Finset (Sym2 (Fin (n+1)))} (hD : IsTriangulation (n+1) D) :
    ∃ (v : Fin (n+1)) (e : Fin n ↪ Fin (n+1)) (l r : Fin n),
      IsTriangulation n (pullback e D) ∧
      (∀ w, w ≠ v → ∃ i, e i = w) ∧ (∀ i, e i ≠ v) ∧ l ≠ r ∧
      (∀ a b, IsEdge (pullback e D) s(a,b) ↔ IsEdge D s(e a,e b)) ∧
      (∀ w, IsEdge D s(v,w) ↔ w = e l ∨ w = e r) ∧
      IsEdge (pullback e D) s(l,r) ∧
      triangles (n+1) D = insert {v,e l,e r} (mapFaces e (triangles n (pullback e D))) := by
  obtain ⟨v,hv0,hvn,hsmall,hedge,hnb⟩ := exists_deleted_triangulation hn hD
  let e : Fin n ↪ Fin (n+1) := ⟨v.succAbove,(Fin.strictMono_succAbove v).injective⟩
  let l : Fin n := ⟨v.val-1,by omega⟩
  let r : Fin n := ⟨v.val,hvn⟩
  have hl : l.val = v.val-1 := rfl
  have hr : r.val = v.val := rfl
  have hel : (e l).val+1 = v.val := by
    have h := succAbove_value v l
    change (v.succAbove l).val+1=v.val
    split_ifs at h <;> omega
  have her : (e r).val = v.val+1 := by
    have h := succAbove_value v r
    change (v.succAbove r).val=v.val+1
    split_ifs at h <;> omega
  have hlr : l ≠ r := by intro h; have := congrArg Fin.val h; omega
  have hnb' : ∀ w, IsEdge D s(v,w) ↔ w = e l ∨ w = e r := by
    intro w
    rw [hnb]
    constructor
    · rintro (h | h)
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    · rintro (rfl | rfl) <;> omega
  have hbase : IsEdge (pullback e D) s(l,r) := by
    apply Or.inl
    apply (boundary_mk_iff hn l r).mpr
    omega
  have havoid : ∀ i, e i ≠ v := fun i => Fin.succAbove_ne v i
  have hrange : ∀ w, w ≠ v → ∃ i, e i = w := fun _ h => Fin.exists_succAbove_eq h
  refine ⟨v,e,l,r,hsmall,hrange,havoid,hlr,hedge,hnb',hbase,?_⟩
  exact triangles_delete_eq v e hrange havoid D (pullback e D) hedge l r hlr hnb' hbase

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarReduction

-- BEGIN COMPLETE MODULE EarStep
section

namespace ChvatalArtGallery.FanPartition.Proof

structure EarStep {n : ℕ} (C : Finset (Sym2 (Fin n)))
    (D : Finset (Sym2 (Fin (n+1)))) where
  vertex : Fin (n+1)
  embed : Fin n ↪ Fin (n+1)
  left : Fin n
  right : Fin n
  distinct : left ≠ right
  avoid : ∀ i, embed i ≠ vertex
  covers : ∀ w, w ≠ vertex → ∃ i, embed i = w
  edge : ∀ a b, IsEdge C s(a,b) ↔ IsEdge D s(embed a,embed b)
  neighbours : ∀ w, IsEdge D s(vertex,w) ↔ w = embed left ∨ w = embed right
  base : IsEdge C s(left,right)
  faces : triangles (n+1) D = insert {vertex,embed left,embed right} (mapFaces embed (triangles n C))

namespace EarStep
variable {n : ℕ} {C : Finset (Sym2 (Fin n))} {D : Finset (Sym2 (Fin (n+1)))}
variable (H : EarStep C D)

def face : Finset (Fin (n+1)) := {H.vertex,H.embed H.left,H.embed H.right}

lemma face_mem : H.face ∈ triangles (n+1) D := by
  rw [H.faces]
  exact Finset.mem_insert_self _ _

lemma vertex_not_map (T : Finset (Fin n)) : H.vertex ∉ T.map H.embed := by
  intro h
  obtain ⟨a,_,ha⟩ := Finset.mem_map.mp h
  exact H.avoid a ha

lemma face_ne_map (T : Finset (Fin n)) : H.face ≠ T.map H.embed := by
  intro he
  have : H.vertex ∈ H.face := by simp [face]
  exact H.vertex_not_map T (he ▸ this)

lemma map_mem {T : Finset (Fin n)} (hT : T ∈ triangles n C) :
    T.map H.embed ∈ triangles (n+1) D := by
  rw [H.faces]
  exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨T,hT,rfl⟩)

lemma face_adjacent {T : Finset (Fin n)} (hl : H.left ∈ T) (hr : H.right ∈ T) :
    Adjacent (T.map H.embed) H.face := by
  refine ⟨(H.face_ne_map T).symm,?_⟩
  have hi : T.map H.embed ∩ H.face = {H.embed H.left,H.embed H.right} := by
    ext w
    simp only [Finset.mem_inter,face,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hw,rfl | he | he⟩
      · exact (H.vertex_not_map T hw).elim
      · exact Or.inl he
      · exact Or.inr he
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_map.mpr ⟨H.left,hl,rfl⟩,Or.inr (Or.inl rfl)⟩
      · exact ⟨Finset.mem_map.mpr ⟨H.right,hr,rfl⟩,Or.inr (Or.inr rfl)⟩
  rw [hi]
  simp [H.embed.injective.ne H.distinct]

end EarStep
end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarStep

-- BEGIN COMPLETE MODULE NativeEarStep
section

namespace ChvatalArtGallery.FanPartition.Proof

 theorem exists_earStep {n : ℕ} (hn : 3 ≤ n)
    {D : Finset (Sym2 (Fin (n+1)))} (hD : IsTriangulation (n+1) D) :
    ∃ C, IsTriangulation n C ∧ Nonempty (EarStep C D) := by
  obtain ⟨v,e,l,r,hC,hrange,havoid,hlr,hedge,hnb,hbase,hfaces⟩ := ear_reduction hn hD
  exact ⟨pullback e D,hC,⟨{
    vertex := v
    embed := e
    left := l
    right := r
    distinct := hlr
    avoid := havoid
    covers := hrange
    edge := hedge
    neighbours := hnb
    base := hbase
    faces := hfaces }⟩⟩

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE NativeEarStep

-- BEGIN COMPLETE MODULE EarColour
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma third_colour (a b : Fin 3) : ∃ k : Fin 3, k ≠ a ∧ k ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

namespace EarStep
variable {n : ℕ} {C : Finset (Sym2 (Fin n))} {D : Finset (Sym2 (Fin (n+1)))}

lemma extend_colour (H : EarStep C D) {c : Fin n → Fin 3} (hc : ProperColour C c) :
    ∃ d : Fin (n+1) → Fin 3, ProperColour D d := by
  classical
  obtain ⟨k,hkl,hkr⟩ := third_colour (c H.left) (c H.right)
  let d := Function.extend H.embed c (fun _ => k)
  have he : ∀ a, d (H.embed a) = c a := H.embed.injective.extend_apply c (fun _ => k)
  have hv : d H.vertex = k := Function.extend_apply' c (fun _ => k) _ (by
    rintro ⟨a,ha⟩; exact H.avoid a ha)
  have hcovers : ∀ w, w = H.vertex ∨ ∃ i, w = H.embed i := by
    intro w
    by_cases hw : w = H.vertex
    · exact Or.inl hw
    · obtain ⟨i,hi⟩ := H.covers w hw
      exact Or.inr ⟨i,hi.symm⟩
  refine ⟨d,?_⟩
  intro a b hab hedge
  rcases hcovers a with rfl | ⟨a,rfl⟩ <;> rcases hcovers b with rfl | ⟨b,rfl⟩
  · exact (hab rfl).elim
  · rw [hv,he]
    rcases (H.neighbours _).mp hedge with hh | hh
    · exact H.embed.injective hh ▸ hkl
    · exact H.embed.injective hh ▸ hkr
  · rw [he,hv]
    have hedge' : IsEdge D s(H.vertex,H.embed a) := by simpa only [Sym2.eq_swap] using hedge
    rcases (H.neighbours _).mp hedge' with hh | hh
    · exact (H.embed.injective hh ▸ hkl).symm
    · exact (H.embed.injective hh ▸ hkr).symm
  · rw [he,he]
    exact hc a b (by intro h; exact hab (congrArg H.embed h)) ((H.edge a b).mpr hedge)

end EarStep
end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarColour

-- BEGIN COMPLETE MODULE EarStars
section

namespace ChvatalArtGallery.FanPartition.Proof
namespace EarStep
variable {n : ℕ} {C : Finset (Sym2 (Fin n))} {D : Finset (Sym2 (Fin (n+1)))}
variable (H : EarStep C D)

lemma star_vertex : vertexStar D H.vertex = {H.face} := by
  ext T
  rw [mem_vertexStar,Finset.mem_singleton,H.faces]
  constructor
  · rintro ⟨hT,hv⟩
    rcases Finset.mem_insert.mp hT with he | hm
    · exact he
    · obtain ⟨U,_,rfl⟩ := Finset.mem_map.mp hm
      exact (H.vertex_not_map U hv).elim
  · intro he
    subst T
    exact ⟨Finset.mem_insert_self _ _,by simp [face]⟩

lemma star_embed (i : Fin n) : vertexStar D (H.embed i) =
    if i = H.left ∨ i = H.right then insert H.face (mapFaces H.embed (vertexStar C i))
    else mapFaces H.embed (vertexStar C i) := by
  classical
  have hface : H.embed i ∈ H.face ↔ i = H.left ∨ i = H.right := by
    simp [face,H.avoid i]
  have hmap : ∀ T, T ∈ mapFaces H.embed (vertexStar C i) ↔
      T ∈ mapFaces H.embed (triangles n C) ∧ H.embed i ∈ T := by
    intro T
    constructor
    · intro hT
      obtain ⟨U,hU,rfl⟩ := Finset.mem_map.mp hT
      have hu := mem_vertexStar.mp hU
      exact ⟨Finset.mem_map.mpr ⟨U,hu.1,rfl⟩,by simpa [faceEmbedding] using hu.2⟩
    · rintro ⟨hT,hi⟩
      obtain ⟨U,hU,rfl⟩ := Finset.mem_map.mp hT
      exact Finset.mem_map.mpr ⟨U,mem_vertexStar.mpr ⟨hU,by simpa [faceEmbedding] using hi⟩,rfl⟩
  ext T
  rw [mem_vertexStar,H.faces]
  by_cases hi : i = H.left ∨ i = H.right
  · simp only [if_pos hi,Finset.mem_insert,hmap]
    constructor
    · rintro ⟨he | hm,hv⟩
      · exact Or.inl he
      · exact Or.inr ⟨hm,hv⟩
    · rintro (he | ⟨hm,hv⟩)
      · subst T; exact ⟨Or.inl rfl,hface.mpr hi⟩
      · exact ⟨Or.inr hm,hv⟩
  · simp only [if_neg hi,hmap,Finset.mem_insert]
    constructor
    · rintro ⟨he | hm,hv⟩
      · subst T; exact (hi (hface.mp hv)).elim
      · exact ⟨hm,hv⟩
    · rintro ⟨hm,hv⟩; exact ⟨Or.inr hm,hv⟩

include H in
lemma stars_nonempty (hn : ∀ i, (vertexStar C i).Nonempty) :
    ∀ v, (vertexStar D v).Nonempty := by
  intro v
  by_cases hv : v = H.vertex
  · subst v; rw [H.star_vertex]; exact Finset.singleton_nonempty _
  · obtain ⟨i,rfl⟩ := H.covers v hv
    rw [H.star_embed]
    split_ifs
    · exact Finset.insert_nonempty _ _
    · obtain ⟨T,hT⟩ := hn i
      exact ⟨T.map H.embed,Finset.mem_map.mpr ⟨T,hT,rfl⟩⟩

lemma stars_connected (hc : ∀ i, DualConnected (vertexStar C i))
    (hbase : ∃ T ∈ triangles n C, H.left ∈ T ∧ H.right ∈ T) :
    ∀ v, DualConnected (vertexStar D v) := by
  intro v
  by_cases hv : v = H.vertex
  · subst v; rw [H.star_vertex]; exact dualConnected_singleton _
  · obtain ⟨i,rfl⟩ := H.covers v hv
    rw [H.star_embed]
    have hm := dualConnected_map H.embed (hc i)
    split_ifs with hi
    · obtain ⟨T,hT,hl,hr⟩ := hbase
      apply dualConnected_insert hm
      · exact Finset.mem_map.mpr ⟨T,mem_vertexStar.mpr ⟨hT,hi.elim (fun h => h ▸ hl) (fun h => h ▸ hr)⟩,rfl⟩
      · exact H.face_adjacent hl hr
    · exact hm

end EarStep
end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarStars

-- BEGIN COMPLETE MODULE EarIncidence
section

namespace ChvatalArtGallery.FanPartition.Proof

def EdgeIncidence {n : ℕ} (D : Finset (Sym2 (Fin n))) : Prop :=
  ∀ a b, a ≠ b → IsEdge D s(a,b) → ∃ T ∈ triangles n D, a ∈ T ∧ b ∈ T

namespace EarStep
variable {n : ℕ} {C : Finset (Sym2 (Fin n))} {D : Finset (Sym2 (Fin (n+1)))}

lemma edge_incidence (H : EarStep C D) (hc : EdgeIncidence C) : EdgeIncidence D := by
  have hcover : ∀ w, w = H.vertex ∨ ∃ i, w = H.embed i := by
    intro w
    by_cases hw : w = H.vertex
    · exact Or.inl hw
    · obtain ⟨i,hi⟩ := H.covers w hw
      exact Or.inr ⟨i,hi.symm⟩
  intro a b hab he
  rcases hcover a with rfl | ⟨a,rfl⟩ <;> rcases hcover b with rfl | ⟨b,rfl⟩
  · exact (hab rfl).elim
  · refine ⟨H.face,H.face_mem,by simp [face],?_⟩
    rcases (H.neighbours _).mp he with hh | hh <;> simp [face,hh]
  · refine ⟨H.face,H.face_mem,?_,by simp [face]⟩
    have he' : IsEdge D s(H.vertex,H.embed a) := by simpa only [Sym2.eq_swap] using he
    rcases (H.neighbours _).mp he' with hh | hh <;> simp [face,hh]
  · obtain ⟨T,hT,ha,hb⟩ := hc a b (by intro h; exact hab (congrArg H.embed h)) ((H.edge _ _).mpr he)
    exact ⟨T.map H.embed,H.map_mem hT,Finset.mem_map.mpr ⟨a,ha,rfl⟩,
      Finset.mem_map.mpr ⟨b,hb,rfl⟩⟩

end EarStep
end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE EarIncidence

-- BEGIN COMPLETE MODULE TriangleBase
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma triangles_three (D : Finset (Sym2 (Fin 3))) : triangles 3 D = {Finset.univ} := by
  ext T
  rw [Finset.mem_singleton]
  constructor
  · intro hT
    apply Finset.eq_univ_of_card
    simpa using (mem_triangles_iff.mp hT).1
  · intro he
    subst T
    apply mem_triangles_iff.mpr
    refine ⟨by simp,?_⟩
    intro a _ b _ hab
    apply Or.inl
    apply (boundary_mk_iff (by decide) a b).mpr
    have ha := a.isLt
    have hb := b.isLt
    have hn : a.val ≠ b.val := by intro h; exact hab (Fin.ext h)
    omega

lemma base_structure (D : Finset (Sym2 (Fin 3))) :
    (∃ c, ProperColour D c) ∧
    (∀ v, (vertexStar D v).Nonempty ∧ DualConnected (vertexStar D v)) ∧ EdgeIncidence D := by
  have hs : ∀ v, vertexStar D v = {Finset.univ} := by
    intro v
    simp [vertexStar,triangles_three]
  refine ⟨⟨id,fun _ _ h _ => h⟩,?_,?_⟩
  · intro v
    rw [hs]
    exact ⟨Finset.singleton_nonempty _,dualConnected_singleton _⟩
  · intro a b _ _
    refine ⟨Finset.univ,?_,Finset.mem_univ _,Finset.mem_univ _⟩
    rw [triangles_three]
    exact Finset.mem_singleton_self _

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE TriangleBase

-- BEGIN COMPLETE MODULE TriangulationStructure
section

namespace ChvatalArtGallery.FanPartition.Proof

lemma triangulation_structure (n : ℕ) (hn : 3 ≤ n) :
    ∀ (D : Finset (Sym2 (Fin n))), IsTriangulation n D →
    (∃ c, ProperColour D c) ∧
    (∀ v, (vertexStar D v).Nonempty ∧ DualConnected (vertexStar D v)) ∧ EdgeIncidence D := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro D _
      exact base_structure D
  | succ n hn ih =>
      intro D hD
      obtain ⟨C,hC,⟨H⟩⟩ := exists_earStep hn hD
      obtain ⟨⟨c,hc⟩,hs,he⟩ := ih C hC
      refine ⟨H.extend_colour hc,?_,H.edge_incidence he⟩
      intro v
      exact ⟨H.stars_nonempty (fun i => (hs i).1) v,
        H.stars_connected (fun i => (hs i).2) (he H.left H.right H.distinct H.base) v⟩

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE TriangulationStructure

-- BEGIN COMPLETE MODULE ColourPartition
section

namespace ChvatalArtGallery.FanPartition.Proof
variable {n : ℕ} {D : Finset (Sym2 (Fin n))}

lemma least_colour_class (c : Fin n → Fin 3) :
    ∃ k : Fin 3, (Finset.univ.filter (fun v => c v = k)).card ≤ n / 3 := by
  classical
  let N := fun k : Fin 3 => (Finset.univ.filter (fun v => c v = k)).card
  obtain ⟨k,_,hk⟩ := Finset.exists_min_image Finset.univ N Finset.univ_nonempty
  have hs : n = ∑ j : Fin 3, N j := by
    simpa [N] using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 3)))
      (f := c) (by intro a _; exact Finset.mem_univ _))
  have hb : 3 * N k ≤ n := by
    rw [hs]
    calc
      3 * N k = ∑ _j : Fin 3, N k := by simp
      _ ≤ ∑ j : Fin 3, N j := Finset.sum_le_sum (fun j hj => hk j hj)
  refine ⟨k,?_⟩
  change N k ≤ n / 3
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr (by omega)

lemma partition_from_colouring (c : Fin n → Fin 3) (hc : ProperColour D c)
    (hn : ∀ v, (vertexStar D v).Nonempty)
    (hconn : ∀ v, DualConnected (vertexStar D v)) :
    ∃ P, IsFanPartition n D P ∧ P.card ≤ n / 3 := by
  classical
  obtain ⟨k,hk⟩ := least_colour_class c
  let C := Finset.univ.filter (fun v => c v = k)
  let P := C.image (vertexStar D)
  refine ⟨P,⟨?_,?_,?_⟩,le_trans (Finset.card_image_le) hk⟩
  · intro F hF
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hF
    exact vertexStar_fan (hn v) (hconn v)
  · intro F hF G hG hne
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hG
    apply Finset.disjoint_left.mpr
    intro T hTv hTw
    have hvm := mem_vertexStar.mp hTv
    have hwm := mem_vertexStar.mp hTw
    have hvw : v ≠ w := by intro he; subst w; exact hne rfl
    apply hc v w hvw ((mem_triangles_iff.mp hvm.1).2 v hvm.2 w hwm.2 hvw)
    exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
  · apply Finset.ext
    intro T
    constructor
    · intro hT
      obtain ⟨F,hF,hTF⟩ := Finset.mem_biUnion.mp hT
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hF
      exact (mem_vertexStar.mp hTF).1
    · intro hT
      obtain ⟨v,hv,hcV⟩ := triangle_colour_exists hc hT k
      exact Finset.mem_biUnion.mpr ⟨vertexStar D v,
        Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcV⟩,rfl⟩,
        mem_vertexStar.mpr ⟨hT,hv⟩⟩

end ChvatalArtGallery.FanPartition.Proof
end
-- END COMPLETE MODULE ColourPartition

-- BEGIN COMPLETE MODULE FanRoot
section

namespace ChvatalArtGallery.FanPartition

theorem triangulation_partition_into_fans (n : ℕ) (hn : 3 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) :
    ∃ P : Finset (Finset (Finset (Fin n))), IsFanPartition n D P ∧ P.card ≤ n / 3 := by
  obtain ⟨⟨c,hc⟩,hs,_⟩ := Proof.triangulation_structure n hn D hD
  exact Proof.partition_from_colouring c hc (fun v => (hs v).1) (fun v => (hs v).2)

end ChvatalArtGallery.FanPartition

theorem solution (n : ℕ) (hn : 3 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : ChvatalArtGallery.FanPartition.IsTriangulation n D) :
    ∃ P : Finset (Finset (Finset (Fin n))),
      ChvatalArtGallery.FanPartition.IsFanPartition n D P ∧ P.card ≤ n / 3 :=
  ChvatalArtGallery.FanPartition.triangulation_partition_into_fans n hn D hD
end
-- END COMPLETE MODULE FanRoot
