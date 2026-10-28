-- Prove2me | solution 1 for CClosedGraphs.Peeling.moon_moser
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T04:06:50.559438+00:00
-- url     : https://prove2.me/submissions/179f4021-5d01-4dd2-86f3-59cab52de98c

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace Prove2SwarmSubmission

open CClosedGraphs.Peeling

set_option autoImplicit false

namespace CClosedGraphs.Peeling
namespace MoonMoser

open Classical
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma mem_maxCliquesIn_iff {G : SimpleGraph V} {W : Set V} {K : Finset V} :
    K ∈ maxCliquesIn G W ↔
      (↑K : Set V) ⊆ W ∧ G.IsClique (↑K : Set V) ∧
      ∀ ⦃T : Finset V⦄, (↑T : Set V) ⊆ W →
        G.IsClique (↑T : Set V) → K ⊆ T → T ⊆ K := by
  classical
  rw [maxCliquesIn]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [Maximal]
  constructor
  · rintro ⟨⟨hKW, hKclique⟩, hKmax⟩
    exact ⟨hKW, hKclique, fun T hTW hTclique hKT => hKmax ⟨hTW, hTclique⟩ hKT⟩
  · rintro ⟨hKW, hKclique, hKmax⟩
    exact ⟨⟨hKW, hKclique⟩, fun T hT hKT => hKmax hT.1 hT.2 hKT⟩

omit [DecidableEq V] in
lemma maxCliquesIn_empty (G : SimpleGraph V) :
    maxCliquesIn G (∅ : Set V) = {∅} := by
  classical
  ext K
  rw [mem_maxCliquesIn_iff]
  constructor
  · rintro ⟨hKW, -, -⟩
    rw [Finset.mem_singleton]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    exact hKW (by exact_mod_cast hx)
  · intro hK
    rw [Finset.mem_singleton] at hK
    subst K
    simp

lemma ncard_inter_add_ncard_diff (s t : Set V) :
    (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card',
    Set.ncard_eq_toFinset_card']
  rw [Set.toFinset_inter, Set.toFinset_sdiff]
  exact Finset.card_inter_add_card_sdiff s.toFinset t.toFinset

lemma exists_mem_diff_neighborSet_of_mem_maxCliquesIn {G : SimpleGraph V} {W : Set V} {v : V}
    (hvW : v ∈ W) {K : Finset V} (hK : K ∈ maxCliquesIn G W) :
    ∃ u ∈ W \ G.neighborSet v, u ∈ K := by
  classical
  by_contra h
  rw [not_exists] at h
  rw [mem_maxCliquesIn_iff] at hK
  rcases hK with ⟨hKW, hKclique, hKmax⟩
  have hKsubN : (↑K : Set V) ⊆ G.neighborSet v := by
    intro x hxK
    by_contra hxN
    apply h x
    exact ⟨⟨hKW (by exact_mod_cast hxK), hxN⟩, by exact_mod_cast hxK⟩
  have hvK : v ∉ K := by
    intro hvKin
    have : v ∈ G.neighborSet v := hKsubN (by exact_mod_cast hvKin)
    exact G.irrefl this
  let T : Finset V := insert v K
  have hTdom : (↑T : Set V) ⊆ W := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hxK
    · exact hvW
    · exact hKW (by exact_mod_cast hxK)
  have hTclique : G.IsClique (↑T : Set V) := by
    dsimp [T]
    rw [Finset.coe_insert]
    exact hKclique.insert (fun x hx _ => hKsubN (by exact_mod_cast hx))
  have hTK : T ⊆ K := hKmax hTdom hTclique (Finset.subset_insert _ _)
  exact hvK (hTK (by simp [T]))


omit [Fintype V] in
lemma card_le_sum_card_filter (s : Finset (Finset V)) (D : Finset V)
    (h : ∀ K ∈ s, ∃ u ∈ D, u ∈ K) :
    s.card ≤ ∑ u ∈ D, (s.filter (fun K => u ∈ K)).card := by
  classical
  calc
    s.card ≤ (D.biUnion (fun u => s.filter (fun K => u ∈ K))).card := by
      apply Finset.card_le_card
      intro K hK
      rw [Finset.mem_biUnion]
      rcases h K hK with ⟨u, huD, huK⟩
      exact ⟨u, huD, by simp [hK, huK]⟩
    _ ≤ ∑ u ∈ D, (s.filter (fun K => u ∈ K)).card :=
      Finset.card_biUnion_le


lemma erase_mem_maxCliquesIn_neighborSet {G : SimpleGraph V} {W : Set V} {v : V}
    {K : Finset V}
    (hK : K ∈ (maxCliquesIn G W).filter (fun K => v ∈ K)) :
    K.erase v ∈ maxCliquesIn G (W ∩ G.neighborSet v) := by
  classical
  have hKmem : K ∈ maxCliquesIn G W := (Finset.mem_filter.mp hK).1
  have hvK : v ∈ K := (Finset.mem_filter.mp hK).2
  rw [mem_maxCliquesIn_iff] at hKmem ⊢
  rcases hKmem with ⟨hKW, hKclique, hKmax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_erase] at hx
    have hxK : x ∈ K := hx.2
    have hxW : x ∈ W := hKW (by exact_mod_cast hxK)
    have hxN : x ∈ G.neighborSet v := by
      rw [SimpleGraph.mem_neighborSet]
      exact G.adj_symm (hKclique hxK hvK hx.1)
    exact ⟨hxW, hxN⟩
  · exact hKclique.subset (by
      intro x hx
      exact (Finset.mem_erase.mp hx).2)
  · intro T hTdom hTclique hKeraseT
    let U : Finset V := insert v T
    have hUdom : (↑U : Set V) ⊆ W := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hxT
      · exact hKW hvK
      · exact (hTdom (by exact_mod_cast hxT)).1
    have hUclique : G.IsClique (↑U : Set V) := by
      dsimp [U]
      rw [Finset.coe_insert]
      exact hTclique.insert (fun x hx _ =>
        ((SimpleGraph.mem_neighborSet G v x).mp ((hTdom (by exact_mod_cast hx)).2)))
    have hKsubU : K ⊆ U := by
      intro x hxK
      by_cases hxv : x = v
      · rw [Finset.mem_insert]
        exact Or.inl hxv
      · rw [Finset.mem_insert]
        right
        exact hKeraseT (by
          rw [Finset.mem_erase]
          exact ⟨hxv, hxK⟩)
    have hUsubK : U ⊆ K := hKmax hUdom hUclique hKsubU
    intro x hxT
    rw [Finset.mem_erase]
    refine ⟨?_, hUsubK ?_⟩
    · have hxN : x ∈ G.neighborSet v := (hTdom (by exact_mod_cast hxT)).2
      exact (G.ne_of_adj (((SimpleGraph.mem_neighborSet G v x).mp hxN))).symm
    · rw [Finset.mem_insert]
      exact Or.inr hxT

lemma insert_mem_maxCliquesIn_of_mem_neighborSet {G : SimpleGraph V} {W : Set V} {v : V}
    {L : Finset V}
    (hL : L ∈ maxCliquesIn G (W ∩ G.neighborSet v))
    (hvW : v ∈ W) :
    insert v L ∈ maxCliquesIn G W := by
  classical
  rw [mem_maxCliquesIn_iff] at hL ⊢
  rcases hL with ⟨hLdom, hLclique, hLmax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hxL
    · exact hvW
    · exact (hLdom (by exact_mod_cast hxL)).1
  · rw [Finset.coe_insert]
    exact hLclique.insert (fun x hx _ =>
      ((SimpleGraph.mem_neighborSet G v x).mp ((hLdom (by exact_mod_cast hx)).2)))
  · intro T hTW hTclique hInsLT
    have hvT : v ∈ T := hInsLT (by rw [Finset.mem_insert]; exact Or.inl rfl)
    have hEraseDom : (↑(T.erase v) : Set V) ⊆ W ∩ G.neighborSet v := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_erase] at hx
      refine ⟨hTW (by exact_mod_cast hx.2), ?_⟩
      rw [SimpleGraph.mem_neighborSet]
      exact hTclique hvT hx.2 hx.1.symm
    have hEraseClique : G.IsClique (↑(T.erase v) : Set V) :=
      hTclique.subset (by
        intro x hx
        exact (Finset.mem_erase.mp hx).2)
    have hLsubErase : L ⊆ T.erase v := by
      intro x hxL
      rw [Finset.mem_erase]
      refine ⟨?_, hInsLT ?_⟩
      · have hxN : x ∈ G.neighborSet v := (hLdom (by exact_mod_cast hxL)).2
        exact (G.ne_of_adj (((SimpleGraph.mem_neighborSet G v x).mp hxN))).symm
      · rw [Finset.mem_insert]
        exact Or.inr hxL
    have hEraseSubL : T.erase v ⊆ L := hLmax hEraseDom hEraseClique hLsubErase
    intro x hxT
    by_cases hxv : x = v
    · rw [Finset.mem_insert]
      exact Or.inl hxv
    · rw [Finset.mem_insert]
      right
      exact hEraseSubL (by
        rw [Finset.mem_erase]
        exact ⟨hxv, hxT⟩)

theorem card_maxCliques_mem_eq (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((maxCliquesIn G W).filter (fun K => v ∈ K)).card =
      numMaxCliquesIn G (W ∩ G.neighborSet v) := by
  classical
  rw [numMaxCliquesIn]
  refine Finset.card_bij'
    (fun K _ => K.erase v) (fun L _ => insert v L) ?_ ?_ ?_ ?_
  · intro K hK
    exact erase_mem_maxCliquesIn_neighborSet hK
  · intro L hL
    exact Finset.mem_filter.mpr
      ⟨insert_mem_maxCliquesIn_of_mem_neighborSet hL hv, by simp⟩
  · intro K hK
    exact Finset.insert_erase (Finset.mem_filter.mp hK).2
  · intro L hL
    have hLdom : (↑L : Set V) ⊆ W ∩ G.neighborSet v :=
      (mem_maxCliquesIn_iff.mp hL).1
    have hvL : v ∉ L := by
      intro hvIn
      have hmem : v ∈ W ∩ G.neighborSet v := hLdom (by exact_mod_cast hvIn)
      exact G.irrefl ((SimpleGraph.mem_neighborSet G v v).mp hmem.2)
    exact Finset.erase_insert hvL


lemma nat_cube_le_three_pow (m : ℕ) : m ^ 3 ≤ 3 ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 3
    · interval_cases m <;> norm_num
    · have hm3 : 3 ≤ m := by omega
      have hprev : (m - 1) ^ 3 ≤ 3 ^ (m - 1) := ih (m - 1) (by omega)
      have hmul : m ^ 3 ≤ 3 * (m - 1) ^ 3 := by
        have hcast : (m : ℤ) ^ 3 ≤ 3 * ((m - 1 : ℕ) : ℤ) ^ 3 := by
          have hsub : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
          rw [hsub]
          ring_nf
          nlinarith [sq_nonneg ((m : ℤ) - 3), sq_nonneg ((m : ℤ) - 4)]
        exact_mod_cast hcast
      calc
        m ^ 3 ≤ 3 * (m - 1) ^ 3 := hmul
        _ ≤ 3 * 3 ^ (m - 1) := Nat.mul_le_mul_left 3 hprev
        _ = 3 ^ m := by
          rw [show 3 * 3 ^ (m - 1) = 3 ^ ((m - 1) + 1) by
            rw [pow_succ]
            ring]
          rw [show (m - 1) + 1 = m by omega]

lemma natCast_le_three_rpow_div_three (m : ℕ) :
    (m : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 3) := by
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hb_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 3) :=
    Real.rpow_nonneg (by norm_num) _
  have hcube_nat : (m : ℝ) ^ 3 ≤ (3 : ℝ) ^ m := by
    exact_mod_cast nat_cube_le_three_pow m
  have hrhs : ((3 : ℝ) ^ ((m : ℝ) / 3)) ^ 3 = (3 : ℝ) ^ m := by
    have hstep : ((3 : ℝ) ^ ((m : ℝ) / 3)) ^ 3 = (3 : ℝ) ^ (m : ℝ) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ ((m : ℝ) / 3)) 3]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    exact hstep.trans (Real.rpow_natCast (3 : ℝ) m)
  apply (pow_le_pow_iff_left₀ hm_nonneg hb_nonneg (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hrhs]
  exact hcube_nat

lemma mul_rpow_le_of_le (d k : ℕ) (h : d ≤ k) :
    (d : ℝ) * (3 : ℝ) ^ ((((k - d : ℕ) : ℝ)) / 3) ≤
      (3 : ℝ) ^ ((k : ℝ) / 3) := by
  have hcast : ((k - d : ℕ) : ℝ) = (k : ℝ) - (d : ℝ) := Nat.cast_sub h
  rw [hcast]
  have hd := natCast_le_three_rpow_div_three d
  have hfac_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (((k : ℝ) - (d : ℝ)) / 3) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (d : ℝ) * (3 : ℝ) ^ (((k : ℝ) - (d : ℝ)) / 3)
        ≤ (3 : ℝ) ^ ((d : ℝ) / 3) *
            (3 : ℝ) ^ (((k : ℝ) - (d : ℝ)) / 3) :=
          mul_le_mul_of_nonneg_right hd hfac_nonneg
    _ = (3 : ℝ) ^ ((d : ℝ) / 3 + ((k : ℝ) - (d : ℝ)) / 3) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = (3 : ℝ) ^ ((k : ℝ) / 3) := by
          congr 1
          ring


theorem moon_moser_aux (G : SimpleGraph V) (W : Set V) :
    (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ W : Set V, W.ncard = k →
      (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3)
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro W hWk
      by_cases hWempty : W = ∅
      · subst W
        rw [numMaxCliquesIn, maxCliquesIn_empty]
        norm_num
      · have hWne : W.Nonempty := Set.nonempty_iff_ne_empty.mpr hWempty
        rcases Finset.exists_min_image W.toFinset
            (fun u => (W \ G.neighborSet u).ncard)
            (by simpa [Set.toFinset_nonempty] using hWne) with ⟨v, hvF, hvmin⟩
        have hvW : v ∈ W := by simpa using hvF
        have hmin : ∀ u ∈ W, (W \ G.neighborSet v).ncard ≤
            (W \ G.neighborSet u).ncard := by
          intro u hu
          exact hvmin u (by simpa using hu)
        let D : Set V := W \ G.neighborSet v
        have hvD : v ∈ D := by
          dsimp [D]
          refine ⟨hvW, ?_⟩
          rw [SimpleGraph.mem_neighborSet]
          exact G.irrefl
        have hDpos : 0 < D.ncard := (Set.ncard_pos (s := D)).mpr ⟨v, hvD⟩
        have hDleW : D ⊆ W := Set.sdiff_subset
        have hDleK : D.ncard ≤ k := by
          rw [← hWk]
          exact Set.ncard_le_ncard hDleW
        let Df : Finset V := D.toFinset
        have hDfcard_nat : Df.card = D.ncard := by
          dsimp [Df]
          exact (Set.ncard_eq_toFinset_card' D).symm
        have hcover : ∀ K ∈ maxCliquesIn G W, ∃ u ∈ D, u ∈ K := by
          intro K hK
          exact exists_mem_diff_neighborSet_of_mem_maxCliquesIn hvW hK
        have hcoverF : ∀ K ∈ maxCliquesIn G W, ∃ u ∈ Df, u ∈ K := by
          intro K hK
          rcases hcover K hK with ⟨u, huD, huK⟩
          exact ⟨u, by simpa [Df] using huD, huK⟩
        have hunion : (maxCliquesIn G W).card ≤
            ∑ u ∈ Df,
              ((maxCliquesIn G W).filter (fun K => u ∈ K)).card :=
          card_le_sum_card_filter (maxCliquesIn G W) Df hcoverF
        have hfiber : ∀ u ∈ Df,
            ((maxCliquesIn G W).filter (fun K => u ∈ K)).card =
              numMaxCliquesIn G (W ∩ G.neighborSet u) := by
          intro u hu
          exact card_maxCliques_mem_eq G W (by
            have huD : u ∈ D := by simpa [Df] using hu
            exact huD.1)
        have hterm : ∀ u ∈ Df,
            (numMaxCliquesIn G (W ∩ G.neighborSet u) : ℝ) ≤
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
          intro u hu
          have huD : u ∈ D := by simpa [Df] using hu
          have huW : u ∈ W := huD.1
          have hminu : D.ncard ≤ (W \ G.neighborSet u).ncard := by
            dsimp [D] at huD
            exact hmin u huW
          have hsplit : (W ∩ G.neighborSet u).ncard +
              (W \ G.neighborSet u).ncard = W.ncard :=
            ncard_inter_add_ncard_diff W (G.neighborSet u)
          have hA_le_k : (W ∩ G.neighborSet u).ncard ≤ k - D.ncard := by
            rw [← hWk]
            omega
          have hlt : (W ∩ G.neighborSet u).ncard < k := by
            have hkpos : 0 < k := by
              rw [← hWk]
              exact (Set.ncard_pos (s := W)).mpr hWne
            omega
          calc
            (numMaxCliquesIn G (W ∩ G.neighborSet u) : ℝ)
                ≤ (3 : ℝ) ^ (((W ∩ G.neighborSet u).ncard : ℝ) / 3) :=
                  ih (W ∩ G.neighborSet u).ncard hlt
                    (W ∩ G.neighborSet u) rfl
            _ ≤ (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
                  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
                  apply div_le_div_of_nonneg_right
                  · exact_mod_cast hA_le_k
                  · norm_num
        have hunionR : ((maxCliquesIn G W).card : ℝ) ≤
            ∑ u ∈ Df,
              (((maxCliquesIn G W).filter (fun K => u ∈ K)).card : ℝ) := by
          exact_mod_cast hunion
        have hsum_le : (∑ u ∈ Df,
              (((maxCliquesIn G W).filter (fun K => u ∈ K)).card : ℝ)) ≤
            ∑ u ∈ Df,
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [hfiber u hu]
          exact hterm u hu
        have hsum_const : (∑ u ∈ Df,
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3)) =
            (D.ncard : ℝ) * (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          exact_mod_cast hDfcard_nat
        calc
          (numMaxCliquesIn G W : ℝ) = ((maxCliquesIn G W).card : ℝ) := rfl
          _ ≤ ∑ u ∈ Df,
              (((maxCliquesIn G W).filter (fun K => u ∈ K)).card : ℝ) := hunionR
          _ ≤ ∑ u ∈ Df,
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := hsum_le
          _ = (D.ncard : ℝ) *
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := hsum_const
          _ ≤ (3 : ℝ) ^ ((k : ℝ) / 3) :=
                mul_rpow_le_of_le D.ncard k hDleK
          _ = (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by rw [hWk]
  exact hP W.ncard W rfl


end MoonMoser

/-- Moon--Moser bound for the number of maximal cliques of a finite induced subgraph,
with the real exponent exactly as in the frozen target. -/
theorem moon_moser {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) :
    (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by
  exact MoonMoser.moon_moser_aux G W

end CClosedGraphs.Peeling

end Prove2SwarmSubmission

open CClosedGraphs.Peeling

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (W : Set V) :
    (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by
  exact Prove2SwarmSubmission.CClosedGraphs.Peeling.moon_moser G W
