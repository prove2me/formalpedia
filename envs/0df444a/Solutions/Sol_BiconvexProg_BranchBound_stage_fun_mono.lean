-- Prove2me | solution 1 for BiconvexProg.BranchBound.stage_fun_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:17:48.242227+00:00
-- url     : https://prove2.me/submissions/c3d736e8-e5cc-440a-8d17-8e335b38fb0a

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

set_option autoImplicit false

namespace P633ff535
open BiconvexProg.BranchBound

variable {n : ℕ}

lemma mem_toSet_iff (B : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    z ∈ B.toSet ↔ (B.l ≤ z.1 ∧ z.1 ≤ B.L) ∧ (B.m ≤ z.2 ∧ z.2 ≤ B.M) := Iff.rfl

lemma subbox_iff (B' B : Box n) :
    B'.IsSubBox B ↔ (B.l ≤ B'.l ∧ B'.L ≤ B.L ∧ B.m ≤ B'.m ∧ B'.M ≤ B.M) := Iff.rfl

lemma subbox_toSet {B' B : Box n} (h : B'.IsSubBox B) : B'.toSet ⊆ B.toSet := by
  intro z hz
  rw [subbox_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [mem_toSet_iff] at hz ⊢
  exact ⟨⟨h1.trans hz.1.1, hz.1.2.trans h2⟩, ⟨h3.trans hz.2.1, hz.2.2.trans h4⟩⟩

lemma subbox_trans {B'' B' B : Box n} (h1 : B''.IsSubBox B') (h2 : B'.IsSubBox B) :
    B''.IsSubBox B := by
  rw [subbox_iff] at *
  exact ⟨h2.1.trans h1.1, h1.2.1.trans h2.2.1, h2.2.2.1.trans h1.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

lemma le_update {x L : Fin n → ℝ} {I : Fin n} {a : ℝ} (h : x ≤ L) (hI : x I ≤ a) :
    x ≤ Function.update L I a := by
  intro i
  by_cases h' : i = I
  · subst h'; simpa using hI
  · simpa [Function.update_of_ne h'] using h i

lemma update_le {x l : Fin n → ℝ} {I : Fin n} {a : ℝ} (h : l ≤ x) (hI : a ≤ x I) :
    Function.update l I a ≤ x := by
  intro i
  by_cases h' : i = I
  · subst h'; simpa using hI
  · simpa [Function.update_of_ne h'] using h i

lemma child_subbox (B : Box n) (I : Fin n) (a b : ℝ) (ha1 : B.l I ≤ a) (ha2 : a ≤ B.L I)
    (hb1 : B.m I ≤ b) (hb2 : b ≤ B.M I) (j : Fin 4) : (B.child I a b j).IsSubBox B := by
  have u1 : B.l ≤ Function.update B.l I a := le_update le_rfl ha1
  have u2 : Function.update B.L I a ≤ B.L := update_le le_rfl ha2
  have u3 : B.m ≤ Function.update B.m I b := le_update le_rfl hb1
  have u4 : Function.update B.M I b ≤ B.M := update_le le_rfl hb2
  fin_cases j
  · exact (subbox_iff _ _).2 ⟨le_rfl, u2, le_rfl, u4⟩
  · exact (subbox_iff _ _).2 ⟨u1, le_rfl, le_rfl, u4⟩
  · exact (subbox_iff _ _).2 ⟨u1, le_rfl, u3, le_rfl⟩
  · exact (subbox_iff _ _).2 ⟨le_rfl, u2, u3, le_rfl⟩

lemma child_cover (B : Box n) (I : Fin n) (a b : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hz : z ∈ B.toSet) : ∃ j : Fin 4, z ∈ (B.child I a b j).toSet := by
  rw [mem_toSet_iff] at hz
  rcases le_total (z.1 I) a with hx | hx <;> rcases le_total (z.2 I) b with hy | hy
  · exact ⟨0, (mem_toSet_iff _ _).2
      ⟨⟨hz.1.1, le_update hz.1.2 hx⟩, ⟨hz.2.1, le_update hz.2.2 hy⟩⟩⟩
  · exact ⟨3, (mem_toSet_iff _ _).2
      ⟨⟨hz.1.1, le_update hz.1.2 hx⟩, ⟨update_le hz.2.1 hy, hz.2.2⟩⟩⟩
  · exact ⟨1, (mem_toSet_iff _ _).2
      ⟨⟨update_le hz.1.1 hx, hz.1.2⟩, ⟨hz.2.1, le_update hz.2.2 hy⟩⟩⟩
  · exact ⟨2, (mem_toSet_iff _ _).2
      ⟨⟨update_le hz.1.1 hx, hz.1.2⟩, ⟨update_le hz.2.1 hy, hz.2.2⟩⟩⟩

lemma mem_split {B0 B : Box n} {I : Fin n} {a b : ℝ} (h : B ∈ B0.split I a b) :
    ∃ j : Fin 4, B = B0.child I a b j := by
  simp only [Box.split, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at h
  rcases h with h | h | h | h <;> exact ⟨_, h⟩

lemma child_mem_split (B0 : Box n) (I : Fin n) (a b : ℝ) (j : Fin 4) :
    B0.child I a b j ∈ B0.split I a b := by
  fin_cases j <;> simp [Box.split]

lemma box_convex (B : Box n) : Convex ℝ B.toSet :=
  (convex_Icc _ _).prod (convex_Icc _ _)

lemma bilin_continuous : Continuous (bilin : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) := by
  unfold bilin
  fun_prop

lemma box_bdd (B : Box n) : ∃ c : ℝ, ∀ w ∈ B.toSet, c ≤ bilin w := by
  have hK : IsCompact B.toSet := isCompact_Icc.prod isCompact_Icc
  obtain ⟨c, hc⟩ := hK.bddBelow_image (bilin_continuous (n := n)).continuousOn
  exact ⟨c, fun w hw => hc ⟨w, hw, rfl⟩⟩

lemma env_set_nonempty {s : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hs : Convex ℝ s) (c : ℝ)
    (hc : ∀ w ∈ s, c ≤ bilin w) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    {r : ℝ | ∃ g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ, ConvexOn ℝ s g ∧ (∀ w ∈ s, g w ≤ bilin w) ∧
      r = g z}.Nonempty :=
  ⟨c, fun _ => c, convexOn_const c hs, hc, rfl⟩

lemma env_set_bdd {s : Set ((Fin n → ℝ) × (Fin n → ℝ))} (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hz : z ∈ s) :
    BddAbove {r : ℝ | ∃ g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ, ConvexOn ℝ s g ∧
      (∀ w ∈ s, g w ≤ bilin w) ∧ r = g z} :=
  ⟨bilin z, by rintro r ⟨g, -, hg, rfl⟩; exact hg z hz⟩

lemma env_le {s : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hs : Convex ℝ s) (c : ℝ)
    (hc : ∀ w ∈ s, c ≤ bilin w) (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ s) :
    convexEnvelope s bilin z ≤ bilin z := by
  unfold convexEnvelope
  exact csSup_le (env_set_nonempty hs c hc z) (by rintro r ⟨g, -, hg, rfl⟩; exact hg z hz)

lemma env_convex {s : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hs : Convex ℝ s) (c : ℝ)
    (hc : ∀ w ∈ s, c ≤ bilin w) : ConvexOn ℝ s (convexEnvelope s bilin) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have h1 : ∀ g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ, ConvexOn ℝ s g → (∀ w ∈ s, g w ≤ bilin w) →
      ∀ v ∈ s, g v ≤ convexEnvelope s bilin v := by
    intro g hg hgle v hv
    unfold convexEnvelope
    exact le_csSup (env_set_bdd v hv) ⟨g, hg, hgle, rfl⟩
  show sSup _ ≤ _
  apply csSup_le (env_set_nonempty hs c hc _)
  rintro r ⟨g, hg, hgle, rfl⟩
  have e1 := h1 g hg hgle x hx
  have e2 := h1 g hg hgle y hy
  calc g (a • x + b • y) ≤ a • g x + b • g y := hg.2 hx hy ha hb hab
    _ ≤ a • convexEnvelope s bilin x + b • convexEnvelope s bilin y := by
      simp only [smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

lemma env_mono {s s' : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hss : s' ⊆ s) (hs : Convex ℝ s)
    (hs' : Convex ℝ s') (c : ℝ) (hc : ∀ w ∈ s, c ≤ bilin w) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hz : z ∈ s') : convexEnvelope s bilin z ≤ convexEnvelope s' bilin z := by
  unfold convexEnvelope
  apply csSup_le_csSup (env_set_bdd z hz) (env_set_nonempty hs c hc z)
  rintro r ⟨g, hg, hgle, rfl⟩
  exact ⟨g, hg.subset hss hs', fun w hw => hgle w (hss hw), rfl⟩

lemma stage_le_node (f g : (Fin n → ℝ) → ℝ) (N : Multiset (Box n)) (B : Box n) (hB : B ∈ N)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ B.toSet) :
    stageFun f g N z ≤ nodeFun f g B z := by
  classical
  unfold stageFun
  apply csInf_le
  · have hfin : {B | B ∈ N ∧ z ∈ B.toSet}.Finite :=
      (N.toFinset.finite_toSet).subset (fun B hB => Multiset.mem_toFinset.2 hB.1)
    exact (hfin.image _).bddBelow
  · exact ⟨B, ⟨hB, hz⟩, rfl⟩

lemma node_le_obj (f g : (Fin n → ℝ) → ℝ) (B : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hz : z ∈ B.toSet) : nodeFun f g B z ≤ objective f g z := by
  obtain ⟨c, hc⟩ := box_bdd B
  have := env_le (box_convex B) c hc z hz
  unfold nodeFun objective
  linarith

lemma inv {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt) :
    ∀ k, (∀ B ∈ nodes k, B.IsSubBox Ω) ∧ (∀ z ∈ Ω.toSet, ∃ B ∈ nodes k, z ∈ B.toSet) := by
  classical
  intro k
  induction k with
  | zero =>
    rw [hrun.init]
    refine ⟨fun B hB => ?_, fun z hz => ⟨Ω, Multiset.mem_singleton_self _, hz⟩⟩
    rw [Multiset.mem_singleton] at hB
    subst hB
    exact (subbox_iff _ _).2 ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  | succ k ih =>
    have hp := ((hrun.pt_mem k).2)
    rw [mem_toSet_iff] at hp
    have hsel := ih.1 _ (hrun.sel_mem k)
    rw [hrun.step k]
    refine ⟨fun B hB => ?_, fun z hz => ?_⟩
    · rcases Multiset.mem_add.1 hB with h | h
      · exact ih.1 B (Multiset.mem_of_mem_erase h)
      · obtain ⟨j, rfl⟩ := mem_split h
        exact subbox_trans (child_subbox _ _ _ _ (hp.1.1 _) (hp.1.2 _) (hp.2.1 _) (hp.2.2 _) j)
          hsel
    · obtain ⟨B, hB, hzB⟩ := ih.2 z hz
      by_cases hBs : B = sel k
      · rw [hBs] at hzB
        obtain ⟨j, hj⟩ := child_cover (sel k) (idx k) ((pt k).1 (idx k)) ((pt k).2 (idx k)) z hzB
        exact ⟨_, Multiset.mem_add.2 (Or.inr (child_mem_split _ _ _ _ j)), hj⟩
      · exact ⟨B, Multiset.mem_add.2 (Or.inl (Multiset.mem_erase_of_ne hBs |>.2 hB)), hzB⟩

end P633ff535

open BiconvexProg.BranchBound Filter Topology P633ff535 in
theorem P633ff535.main_aux {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt) :
    (∀ k, ∀ B ∈ nodes k, ConvexOn ℝ B.toSet (nodeFun f g B)) ∧
    (∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ objective f g z) ∧
    (∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ stageFun f g (nodes (k + 1)) z) ∧
    (∀ z ∈ Ω.toSet, ∃ ψbar : ℝ,
      Tendsto (fun k => stageFun f g (nodes k) z) atTop (𝓝 ψbar) ∧ ψbar ≤ objective f g z) := by
  classical
  have hI := inv hrun
  have P1 : ∀ k, ∀ B ∈ nodes k, ConvexOn ℝ B.toSet (nodeFun f g B) := by
    intro k B hB
    obtain ⟨c, hc⟩ := box_bdd B
    have hsub := (subbox_iff _ _).1 ((hI k).1 B hB)
    have hf : ConvexOn ℝ B.toSet (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f z.1) := by
      have := hP.f_convex.comp_linearMap (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))
      refine this.subset ?_ (box_convex B)
      intro z hz
      rw [mem_toSet_iff] at hz
      show Ω.l ≤ z.1 ∧ z.1 ≤ Ω.L
      exact ⟨hsub.1.trans hz.1.1, hz.1.2.trans hsub.2.1⟩
    have hg : ConvexOn ℝ B.toSet (fun z : (Fin n → ℝ) × (Fin n → ℝ) => g z.2) := by
      have := hP.g_convex.comp_linearMap (LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))
      refine this.subset ?_ (box_convex B)
      intro z hz
      rw [mem_toSet_iff] at hz
      show Ω.m ≤ z.2 ∧ z.2 ≤ Ω.M
      exact ⟨hsub.2.2.1.trans hz.2.1, hz.2.2.trans hsub.2.2.2⟩
    have he := env_convex (box_convex B) c hc
    exact (hf.add he).add hg
  have P2 : ∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ objective f g z := by
    intro k z hz
    obtain ⟨B, hB, hzB⟩ := (hI k).2 z hz
    exact (stage_le_node f g _ B hB z hzB).trans (node_le_obj f g B z hzB)
  have P3 : ∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ stageFun f g (nodes (k + 1)) z := by
    intro k z hz
    have hp := ((hrun.pt_mem k).2)
    rw [mem_toSet_iff] at hp
    obtain ⟨B1, hB1, hzB1⟩ := (hI (k + 1)).2 z hz
    show _ ≤ sInf _
    refine le_csInf ⟨nodeFun f g B1 z, B1, ⟨hB1, hzB1⟩, rfl⟩ ?_
    rintro r ⟨B', ⟨hB', hzB'⟩, rfl⟩
    rw [hrun.step k] at hB'
    rcases Multiset.mem_add.1 hB' with h | h
    · exact stage_le_node f g _ B' (Multiset.mem_of_mem_erase h) z hzB'
    · obtain ⟨j, rfl⟩ := mem_split h
      have hcs := child_subbox (sel k) (idx k) ((pt k).1 (idx k)) ((pt k).2 (idx k))
        (hp.1.1 (idx k)) (hp.1.2 (idx k)) (hp.2.1 (idx k)) (hp.2.2 (idx k)) j
      have hss := subbox_toSet hcs
      have hzs := hss hzB'
      refine (stage_le_node f g _ _ (hrun.sel_mem k) z hzs).trans ?_
      obtain ⟨c, hc⟩ := box_bdd (sel k)
      have := env_mono hss (box_convex _) (box_convex _) c hc z hzB'
      unfold nodeFun
      linarith
  refine ⟨P1, P2, P3, fun z hz => ?_⟩
  have hmono : Monotone (fun k => stageFun f g (nodes k) z) :=
    monotone_nat_of_le_succ (fun k => P3 k z hz)
  have hbdd : BddAbove (Set.range (fun k => stageFun f g (nodes k) z)) :=
    ⟨objective f g z, by rintro _ ⟨k, rfl⟩; exact P2 k z hz⟩
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd, ciSup_le fun k => P2 k z hz⟩

open BiconvexProg.BranchBound Filter Topology in
theorem solution {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt) :
    (∀ k, ∀ B ∈ nodes k, ConvexOn ℝ B.toSet (nodeFun f g B)) ∧
    (∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ objective f g z) ∧
    (∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ stageFun f g (nodes (k + 1)) z) ∧
    (∀ z ∈ Ω.toSet, ∃ ψbar : ℝ,
      Tendsto (fun k => stageFun f g (nodes k) z) atTop (𝓝 ψbar) ∧ ψbar ≤ objective f g z) := by
  exact P633ff535.main_aux hP hrun
