-- Prove2me | solution 1 for CClosedGraphs.Peeling.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T11:13:06.8885+00:00
-- url     : https://prove2.me/submissions/b5cb14ad-d4a9-4d41-9df0-e239d500b1fd

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

noncomputable section
open Finset
namespace PeelingProof
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def cliques (G : SimpleGraph V) (W : Finset V) : Finset (Finset V) :=
  CClosedGraphs.Peeling.maxCliquesIn G (↑W : Set V)
noncomputable def mc (G : SimpleGraph V) (W : Finset V) : ℕ := (cliques G W).card
noncomputable def neighbors (G : SimpleGraph V) (W : Finset V) (v : V) : Finset V :=
  letI := Classical.propDecidable
  W.filter (G.Adj v)
noncomputable def common (G : SimpleGraph V) (W : Finset V) (v u : V) : Finset V :=
  letI := Classical.propDecidable
  W.filter (fun x => G.Adj v x ∧ G.Adj u x)
noncomputable def factor (c : ℕ) : ℝ := (3 : ℝ) ^ (((c : ℝ) - 1) / 3)
end PeelingProof
end

noncomputable section
open Finset
namespace PeelingProof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_cliques_iff (G : SimpleGraph V) (W K : Finset V) :
    K ∈ cliques G W ↔ K ⊆ W ∧ G.IsClique (↑K : Set V) ∧
      ∀ u ∈ W, (∀ x ∈ K, u ≠ x → G.Adj u x) → u ∈ K := by
  classical
  change K ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨h.1.1, h.1.2, ?_⟩
    intro u hu hadj
    have hi : (↑(insert u K) : Set V) ⊆ (↑W : Set V) ∧
        G.IsClique (↑(insert u K) : Set V) := by
      refine ⟨Finset.insert_subset hu h.1.1, ?_⟩
      rw [Finset.coe_insert]
      exact h.1.2.insert hadj
    exact h.2 hi (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
  · rintro ⟨hsub, hcl, hmax⟩
    refine ⟨⟨hsub, hcl⟩, ?_⟩
    intro T hT hKT u hu
    exact hmax u (hT.1 hu) (fun x hx hne => hT.2 hu (hKT hx) hne)

theorem cliques_empty (G : SimpleGraph V) : cliques G ∅ = {∅} := by
  classical
  ext K
  rw [mem_cliques_iff, Finset.mem_singleton]
  constructor
  · intro h
    exact Finset.subset_empty.mp h.1
  · rintro rfl
    simp

theorem mc_empty (G : SimpleGraph V) : mc G ∅ = 1 := by
  simp [mc, cliques_empty]

theorem cliques_singleton (G : SimpleGraph V) (v : V) : cliques G {v} = {{v}} := by
  classical
  ext K
  rw [mem_cliques_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hcl, hm⟩
    apply Finset.Subset.antisymm hsub
    intro x hx
    have hxv : x = v := Finset.mem_singleton.mp hx
    subst x
    exact hm v (Finset.mem_singleton_self v) (by
      intro x hx hne
      have : x = v := Finset.mem_singleton.mp (hsub hx)
      exact (hne this.symm).elim)
  · rintro rfl
    exact ⟨Finset.Subset.refl _, by simp, fun _ hu _ => hu⟩

theorem mc_singleton (G : SimpleGraph V) (v : V) : mc G {v} = 1 := by
  simp [mc, cliques_singleton]

theorem erase_to_neighbors (G : SimpleGraph V) (W K : Finset V) (v : V)
    (hK : K ∈ cliques G W) (hv : v ∈ K) :
    K.erase v ∈ cliques G (neighbors G W v) := by
  classical
  obtain ⟨hsub, hcl, hm⟩ := (mem_cliques_iff G W K).mp hK
  rw [mem_cliques_iff]
  refine ⟨?_, hcl.subset (Finset.erase_subset _ _), ?_⟩
  · intro x hx
    obtain ⟨hxv,hx⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_filter.mpr ⟨hsub hx,hcl hv hx hxv.symm⟩
  · intro u hu hadj
    obtain ⟨huW,hvu⟩ := Finset.mem_filter.mp hu
    have huv : u ≠ v := hvu.ne.symm
    apply Finset.mem_erase.mpr
    refine ⟨huv,hm u huW ?_⟩
    intro x hx hux
    by_cases hxv : x = v
    · subst x
      exact hvu.symm
    · exact hadj x (Finset.mem_erase.mpr ⟨hxv,hx⟩) hux

theorem clique_subset (G : SimpleGraph V) (W K : Finset V) (hK : K ∈ cliques G W) :
    K ⊆ W := ((mem_cliques_iff G W K).mp hK).1

theorem maximal_eq_of_subset (G : SimpleGraph V) (W K T : Finset V)
    (hK : K ∈ cliques G W) (hT : T ∈ cliques G W) (hKT : K ⊆ T) : K = T := by
  obtain ⟨_,_,hm⟩ := (mem_cliques_iff G W K).mp hK
  obtain ⟨hTW,hcl,_⟩ := (mem_cliques_iff G W T).mp hT
  apply Finset.Subset.antisymm hKT
  intro u hu
  exact hm u (hTW hu) (fun x hx hne => hcl hu (hKT hx) hne)

end PeelingProof
end

noncomputable section
open Finset
namespace PeelingProof

theorem card_le_sum_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (S : Finset β) (B : β → Finset α)
    (hcover : ∀ a ∈ A, ∃ b ∈ S, a ∈ B b) :
    A.card ≤ ∑ b ∈ S, (B b).card := by
  have hs : A ⊆ S.biUnion B := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcover a ha
    exact mem_biUnion.mpr ⟨b, hb, hab⟩
  exact (Finset.card_le_card hs).trans Finset.card_biUnion_le

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem containing_le_neighbors (G : SimpleGraph V) (W : Finset V) (u : V) :
    ((cliques G W).filter (fun K => u ∈ K)).card ≤ mc G (neighbors G W u) := by
  classical
  apply Finset.card_le_card_of_injOn (fun K : Finset V => K.erase u)
  · intro K hK
    exact erase_to_neighbors G W K u (mem_filter.mp hK).1 (mem_filter.mp hK).2
  · intro K hK L hL heq
    have hKu := (mem_filter.mp hK).2
    have hLu := (mem_filter.mp hL).2
    calc
      K = insert u (K.erase u) := (insert_erase hKu).symm
      _ = insert u (L.erase u) := congrArg (insert u) heq
      _ = L := insert_erase hLu

theorem clique_branching (G : SimpleGraph V) (W : Finset V) (v : V)
    (hv : v ∈ W) :
    mc G W ≤ ∑ u ∈ W \ neighbors G W v, mc G (neighbors G W u) := by
  classical
  let B := W \ neighbors G W v
  let F := fun u : V => (cliques G W).filter (fun K => u ∈ K)
  have hvB : v ∈ B := by simp [B, neighbors, hv]
  have hcover : ∀ K ∈ cliques G W, ∃ u ∈ B, K ∈ F u := by
    intro K hK
    have hm := (mem_cliques_iff G W K).mp hK
    have hmeet : ∃ u ∈ K, u ∈ B := by
      by_contra h
      push Not at h
      have hAdj : ∀ x ∈ K, v ≠ x → G.Adj v x := by
        intro x hx _
        by_contra hn
        have hxW := hm.1 hx
        have hxB : x ∈ B := by simp [B, neighbors, hxW, hn]
        exact h x hx hxB
      have hvK := hm.2.2 v hv hAdj
      exact h v hvK hvB
    obtain ⟨u, huK, huB⟩ := hmeet
    exact ⟨u, huB, mem_filter.mpr ⟨hK, huK⟩⟩
  calc
    mc G W ≤ ∑ u ∈ B, (F u).card := card_le_sum_card (cliques G W) B F hcover
    _ ≤ ∑ u ∈ B, mc G (neighbors G W u) :=
      Finset.sum_le_sum fun u _ => containing_le_neighbors G W u

end PeelingProof
end

noncomputable section
namespace PeelingProof

theorem nat_cube_le_three_pow (d : ℕ) : (d : ℝ)^3 ≤ (3 : ℝ)^d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    by_cases hd : d < 3
    · interval_cases d <;> norm_num
    · have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 3 ≤ d by omega)
      have hq : 0 ≤ (d : ℝ) - 3 := sub_nonneg.mpr hd3
      have hq2 := sq_nonneg ((d : ℝ) - 3)
      have hq3 : 0 ≤ ((d : ℝ) - 3)^3 := pow_nonneg hq 3
      have hpoly : ((d : ℝ) + 1)^3 ≤ 3 * (d : ℝ)^3 := by nlinarith
      calc
        ((d + 1 : ℕ) : ℝ)^3 = ((d : ℝ) + 1)^3 := by norm_num
        _ ≤ 3 * (d : ℝ)^3 := hpoly
        _ ≤ 3 * (3 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (3 : ℝ)^(d + 1) := by rw [pow_succ]; ring

theorem nat_le_three_rpow (d : ℕ) : (d : ℝ) ≤ (3 : ℝ)^((d : ℝ)/3) := by
  have hp : 0 ≤ (3 : ℝ)^((d : ℝ)/3) := (Real.rpow_pos_of_pos (by norm_num) _).le
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg d) hp (by decide : (3 : ℕ) ≠ 0)).mp
  have heq : ((3 : ℝ)^((d : ℝ)/3))^3 = (3 : ℝ)^d := by
    rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (3 : ℝ))]
    norm_num only [Nat.cast_ofNat]
    rw [show (d : ℝ) / 3 * (3 : ℝ) = (d : ℝ) by ring, Real.rpow_natCast]
  rw [heq]
  exact nat_cube_le_three_pow d

theorem branch_bound (n d : ℕ) (hd : d ≤ n) :
    (d : ℝ) * (3 : ℝ)^(((n-d : ℕ) : ℝ)/3) ≤ (3 : ℝ)^((n : ℝ)/3) := by
  calc
    (d : ℝ) * (3 : ℝ)^(((n-d : ℕ) : ℝ)/3)
        ≤ (3 : ℝ)^((d : ℝ)/3) * (3 : ℝ)^(((n-d : ℕ) : ℝ)/3) :=
      mul_le_mul_of_nonneg_right (nat_le_three_rpow d)
        (Real.rpow_pos_of_pos (by norm_num) _).le
    _ = (3 : ℝ)^((d : ℝ)/3 + ((n-d : ℕ) : ℝ)/3) :=
      (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _).symm
    _ = (3 : ℝ)^((n : ℝ)/3) := by rw [Nat.cast_sub hd]; congr 1; ring

theorem factor_one_le (c : ℕ) (hc : 0 < c) : 1 ≤ factor c := by
  apply Real.one_le_rpow (by norm_num : 1 ≤ (3 : ℝ))
  have h : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  positivity

end PeelingProof
end

noncomputable section
open Finset
namespace PeelingProof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem moon_moser (G : SimpleGraph V) (W : Finset V) :
    (mc G W : ℝ) ≤ (3 : ℝ)^((W.card : ℝ)/3) := by
  classical
  suffices h : ∀ n : ℕ, ∀ W : Finset V, W.card = n →
      (mc G W : ℝ) ≤ (3 : ℝ)^((n : ℝ)/3) from h W.card W rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W hW
    by_cases hn : n = 0
    · have he : W = ∅ := Finset.card_eq_zero.mp (hW.trans hn)
      subst W
      simp [mc_empty, ← hW]
    · have hpos : 0 < W.card := by omega
      obtain ⟨v, hv, hmax⟩ := W.exists_max_image
        (fun u => (neighbors G W u).card) (Finset.card_pos.mp hpos)
      let B := W \ neighbors G W v
      let d := B.card
      have hsub : neighbors G W v ⊆ W := Finset.filter_subset _ _
      have hvB : v ∈ B := by simp [B, neighbors, hv]
      have hdpos : 0 < d := Finset.card_pos.mpr ⟨v, hvB⟩
      have hd : d ≤ n := by
        exact hW ▸ Finset.card_le_card (Finset.sdiff_subset : B ⊆ W)
      have hdEq : d = n - (neighbors G W v).card := by
        dsimp [d, B]
        rw [Finset.card_sdiff_of_subset hsub, hW]
      have hneigh : (neighbors G W v).card = n - d := by
        have := Finset.card_le_card hsub
        omega
      have hbound : ∀ u ∈ B, (mc G (neighbors G W u) : ℝ) ≤
          (3 : ℝ)^(((n-d : ℕ) : ℝ)/3) := by
        intro u hu
        have huW : u ∈ W := (Finset.mem_sdiff.mp hu).1
        have hle : (neighbors G W u).card ≤ n - d := by
          simpa only [hneigh] using hmax u huW
        have hlt : (neighbors G W u).card < n := by omega
        exact (ih _ hlt _ rfl).trans (Real.rpow_le_rpow_of_exponent_le
          (by norm_num : 1 ≤ (3 : ℝ)) (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num)))
      calc
        (mc G W : ℝ) ≤ ∑ u ∈ B, (mc G (neighbors G W u) : ℝ) := by
          exact_mod_cast clique_branching G W v hv
        _ ≤ ∑ _u ∈ B, (3 : ℝ)^(((n-d : ℕ) : ℝ)/3) := Finset.sum_le_sum hbound
        _ = (d : ℝ) * (3 : ℝ)^(((n-d : ℕ) : ℝ)/3) := by simp [d]
        _ ≤ (3 : ℝ)^((n : ℝ)/3) := branch_bound n d hd

end PeelingProof
end

noncomputable section
open Finset
namespace PeelingProof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem erase_maximal_of_not_mem (G : SimpleGraph V) (W K : Finset V) (v : V)
    (hK : K ∈ cliques G W) (hv : v ∉ K) : K.erase v ∈ cliques G (W.erase v) := by
  classical
  rw [Finset.erase_eq_of_notMem hv,mem_cliques_iff]
  obtain ⟨hsub,hcl,hm⟩ := (mem_cliques_iff G W K).mp hK
  exact ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hx),hsub hx⟩,
    hcl,fun u hu hadj => hm u (Finset.mem_of_mem_erase hu) hadj⟩

theorem erase_injective_maximal (G : SimpleGraph V) (W K T : Finset V) (v : V)
    (hK : K ∈ cliques G W) (hT : T ∈ cliques G W)
    (he : K.erase v = T.erase v) : K = T := by
  classical
  by_cases hvK : v ∈ K
  · by_cases hvT : v ∈ T
    · rw [← Finset.insert_erase hvK,he,Finset.insert_erase hvT]
    · apply (maximal_eq_of_subset G W T K hT hK ?_).symm
      rw [← Finset.erase_eq_of_notMem hvT,← he]
      exact Finset.erase_subset _ _
  · apply maximal_eq_of_subset G W K T hK hT
    rw [← Finset.erase_eq_of_notMem hvK,he]
    exact Finset.erase_subset _ _

theorem exceptional_certificate (G : SimpleGraph V) (W K : Finset V) (v : V)
    (hK : K ∈ cliques G W) (hbad : K.erase v ∉ cliques G (W.erase v)) :
    v ∈ K ∧ ∃ u ∈ W, u ≠ v ∧ ¬G.Adj v u ∧
      K.erase v ∈ cliques G (common G W v u) := by
  classical
  have hv : v ∈ K := by
    by_contra h
    exact hbad (erase_maximal_of_not_mem G W K v hK h)
  refine ⟨hv,?_⟩
  obtain ⟨hKW,hcl,hm⟩ := (mem_cliques_iff G W K).mp hK
  have hsub : K.erase v ⊆ W.erase v := Finset.erase_subset_erase v hKW
  have hcle : G.IsClique (↑(K.erase v) : Set V) := hcl.subset (Finset.erase_subset _ _)
  have hnlocal : ¬ ∀ u ∈ W.erase v,
      (∀ x ∈ K.erase v, u ≠ x → G.Adj u x) → u ∈ K.erase v := by
    intro hh
    exact hbad ((mem_cliques_iff _ _ _).mpr ⟨hsub,hcle,hh⟩)
  push Not at hnlocal
  obtain ⟨u,hu,hadj,hun⟩ := hnlocal
  obtain ⟨huv,huW⟩ := Finset.mem_erase.mp hu
  have huK : u ∉ K := fun hh => hun (Finset.mem_erase.mpr ⟨huv,hh⟩)
  have hnv : ¬G.Adj v u := by
    intro hvu
    apply huK
    apply hm u huW
    intro x hx hux
    by_cases hxv : x = v
    · subst x
      exact hvu.symm
    · exact hadj x (Finset.mem_erase.mpr ⟨hxv,hx⟩) hux
  refine ⟨u,huW,huv,hnv,?_⟩
  rw [mem_cliques_iff]
  refine ⟨?_,hcle,?_⟩
  · intro x hx
    obtain ⟨hxv,hxK⟩ := Finset.mem_erase.mp hx
    simp only [common, Finset.mem_filter]
    exact ⟨hKW hxK,hcl hv hxK hxv.symm,
      hadj x hx (fun he => huK (he ▸ hxK))⟩
  · intro x hx hxa
    simp only [common, Finset.mem_filter] at hx
    obtain ⟨hxW,hvx,_⟩ := hx
    refine Finset.mem_erase.mpr ⟨hvx.ne.symm,hm x hxW ?_⟩
    intro y hy hxy
    by_cases hyv : y = v
    · subst y
      exact hvx.symm
    · exact hxa y (Finset.mem_erase.mpr ⟨hyv,hy⟩) hxy

omit [Fintype V] [DecidableEq V] in
theorem common_card_lt (c : ℕ) (G : SimpleGraph V) (W : Finset V) (v u : V)
    (hv : v ∈ W) (hu : u ∈ W) (hne : u ≠ v) (hnadj : ¬G.Adj v u)
    (hgood : ∀ w, ¬ CClosedGraphs.Peeling.IsBadPairIn c G (↑W : Set V) v w) :
    (common G W v u).card < c := by
  classical
  have hs : (↑(common G W v u) : Set V) = (↑W : Set V) ∩ G.commonNeighbors v u := by
    ext x
    simp [common,SimpleGraph.mem_commonNeighbors]
  by_contra h
  apply hgood u
  refine ⟨hv,hu,hne.symm,hnadj,?_⟩
  rw [← hs,Set.ncard_coe_finset]
  exact Nat.le_of_not_gt h

theorem peeling_step (c : ℕ) (hc : 0 < c) (G : SimpleGraph V)
    (W : Finset V) (v : V) (hv : v ∈ W)
    (hgood : ∀ w, ¬ CClosedGraphs.Peeling.IsBadPairIn c G (↑W : Set V) v w) :
    (mc G W : ℝ) ≤ (mc G (W.erase v) : ℝ) + factor c * (W.card : ℝ) := by
  classical
  let R := (cliques G W).filter (fun K => K.erase v ∈ cliques G (W.erase v))
  let E := (cliques G W).filter (fun K => K.erase v ∉ cliques G (W.erase v))
  let U := W.filter (fun u => u ≠ v ∧ ¬G.Adj v u)
  let F := fun u => E.filter (fun K => K.erase v ∈ cliques G (common G W v u))
  have hR : R.card ≤ mc G (W.erase v) := by
    apply Finset.card_le_card_of_injOn (fun K => K.erase v)
    · intro K hK
      exact (Finset.mem_filter.mp hK).2
    · intro K hK T hT he
      exact erase_injective_maximal G W K T v
        (Finset.mem_filter.mp hK).1 (Finset.mem_filter.mp hT).1 he
  have hE : E.card ≤ ∑ u ∈ U, (F u).card := by
    apply card_le_sum_card
    intro K hK
    obtain ⟨hKW,hbad⟩ := Finset.mem_filter.mp hK
    obtain ⟨_,u,huW,huv,hnadj,hcom⟩ := exceptional_certificate G W K v hKW hbad
    exact ⟨u,Finset.mem_filter.mpr ⟨huW,huv,hnadj⟩,Finset.mem_filter.mpr ⟨hK,hcom⟩⟩
  have hF : ∀ u ∈ U, ((F u).card : ℝ) ≤ factor c := by
    intro u hu
    obtain ⟨huW,huv,hnadj⟩ := Finset.mem_filter.mp hu
    have hinj : (F u).card ≤ mc G (common G W v u) := by
      apply Finset.card_le_card_of_injOn (fun K => K.erase v)
      · intro K hK
        exact (Finset.mem_filter.mp hK).2
      · intro K hK T hT he
        exact erase_injective_maximal G W K T v
          (Finset.mem_filter.mp (Finset.mem_filter.mp hK).1).1
          (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).1 he
    have hcard := common_card_lt c G W v u hv huW huv hnadj hgood
    have hexp : ((common G W v u).card : ℝ)/3 ≤ ((c:ℝ)-1)/3 := by
      have hh : (common G W v u).card + 1 ≤ c := hcard
      have hr : ((common G W v u).card : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hh
      linarith
    calc
      ((F u).card : ℝ) ≤ (mc G (common G W v u) : ℝ) := by exact_mod_cast hinj
      _ ≤ (3:ℝ)^(((common G W v u).card:ℝ)/3) := moon_moser G _
      _ ≤ factor c := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsplit : R.card + E.card = mc G W := by
    exact Finset.card_filter_add_card_filter_not _
  have hu : (U.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have ha : 0 ≤ factor c := (factor_one_le c hc).trans' (by norm_num)
  have hes : (E.card : ℝ) ≤ ∑ u ∈ U, ((F u).card : ℝ) := by exact_mod_cast hE
  have her : (E.card : ℝ) ≤ (U.card:ℝ)*factor c := by
    calc
      (E.card:ℝ) ≤ ∑ u ∈ U, ((F u).card:ℝ) := hes
      _ ≤ ∑ _u ∈ U, factor c := Finset.sum_le_sum hF
      _ = (U.card:ℝ)*factor c := by simp
  have hrr : (R.card:ℝ) ≤ mc G (W.erase v) := by exact_mod_cast hR
  have hss : (R.card:ℝ)+(E.card:ℝ) = mc G W := by exact_mod_cast hsplit
  have huu := mul_le_mul_of_nonneg_right hu ha
  nlinarith

end PeelingProof
end

noncomputable section
open Finset
namespace PeelingProof

noncomputable def suffix {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x => k ≤ (σ.symm x).val)

theorem suffix_card {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (suffix σ k).card = n-k := by
  classical
  have he : (suffix σ k).card =
      (Finset.univ.filter (fun x : Fin n => k ≤ x.val)).card :=
    Finset.card_equiv σ.symm (by intro x; simp [suffix])
  rw [he]
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun x : Fin n => x.val < k)
  have hlt : (Finset.univ.filter (fun x : Fin n => x.val < k)).card = k := by
    rw [Fin.card_filter_val_lt, Nat.min_eq_right hk]
  simp only [not_lt] at hpart
  rw [hlt, Finset.card_univ, Fintype.card_fin] at hpart
  omega

theorem suffix_erase {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k < n) :
    (suffix σ k).erase (σ ⟨k,hk⟩) = suffix σ (k+1) := by
  classical
  ext x
  have he : x = σ ⟨k,hk⟩ ↔ (σ.symm x).val = k := by
    constructor
    · rintro rfl
      simp
    · intro h
      have hf : σ.symm x = ⟨k,hk⟩ := Fin.ext h
      exact σ.symm.injective (by simpa using hf)
  simp only [Finset.mem_erase, suffix, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem weak_bound (c n : ℕ) (hc : 0 < c) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : CClosedGraphs.Peeling.IsWeaklyCClosed c G) :
    (mc G Finset.univ : ℝ) ≤ factor c * (n : ℝ)^2 := by
  classical
  obtain ⟨σ, hσ⟩ := hG
  have hA : 0 ≤ factor c := (by norm_num : (0 : ℝ) ≤ 1).trans (factor_one_le c hc)
  have hbound : ∀ m : ℕ, ∀ k : ℕ, k < n → n-k = m →
      (mc G (suffix σ k) : ℝ) ≤ factor c * (m : ℝ)^2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k hk hm
      have hmpos : 0 < m := by omega
      have hcard : (suffix σ k).card = m := (suffix_card σ k hk.le).trans hm
      by_cases hm1 : m = 1
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hcard.trans hm1)
        rw [hv, mc_singleton, hm1]
        norm_num only [Nat.cast_one, one_pow, mul_one]
        exact factor_one_le c hc
      · have hk1 : k+1 < n := by omega
        have hnext : n-(k+1) = m-1 := by omega
        have hi := ih (m-1) (by omega) (k+1) hk1 hnext
        have hv : σ ⟨k,hk⟩ ∈ suffix σ k := by simp [suffix]
        have hg : ∀ w, ¬CClosedGraphs.Peeling.IsBadPairIn c G
            (↑(suffix σ k) : Set (Fin n)) (σ ⟨k,hk⟩) w := by
          intro w
          simpa only [suffix, Finset.coe_filter, Finset.mem_univ,
            true_and, Fin.le_def] using hσ ⟨k,hk⟩ w
        have hs := peeling_step c hc G (suffix σ k) (σ ⟨k,hk⟩) hv hg
        rw [suffix_erase σ k hk, hcard] at hs
        have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
        have hsq : ((m-1 : ℕ) : ℝ)^2 + (m : ℝ) ≤ (m : ℝ)^2 := by
          rw [Nat.cast_sub (by omega : 1 ≤ m)]
          norm_num only [Nat.cast_one]
          nlinarith
        calc
          (mc G (suffix σ k) : ℝ) ≤
              (mc G (suffix σ (k+1)) : ℝ) + factor c * (m : ℝ) := hs
          _ ≤ factor c * ((m-1 : ℕ) : ℝ)^2 + factor c * (m : ℝ) :=
            add_le_add_left hi _
          _ = factor c * (((m-1 : ℕ) : ℝ)^2 + (m : ℝ)) := by ring
          _ ≤ factor c * (m : ℝ)^2 := mul_le_mul_of_nonneg_left hsq hA
  simpa [suffix] using hbound n 0 hn (Nat.sub_zero n)

end PeelingProof
end

namespace CClosedGraphs.Peeling
theorem theorem_2_2 (c n : ℕ) (hc : 0 < c) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hG : IsWeaklyCClosed c G) :
    (numMaxCliques G : ℝ) ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (n : ℝ) ^ 2 := by
  simpa only [PeelingProof.mc, PeelingProof.cliques, numMaxCliques, numMaxCliquesIn,
    Finset.coe_univ, PeelingProof.factor] using PeelingProof.weak_bound c n hc hn G hG
end CClosedGraphs.Peeling

open CClosedGraphs.Peeling

theorem solution (c n : ℕ) (hc : 0 < c) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hG : IsWeaklyCClosed c G) :
    (numMaxCliques G : ℝ) ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (n : ℝ) ^ 2 := by
  exact CClosedGraphs.Peeling.theorem_2_2 c n hc hn G hG
