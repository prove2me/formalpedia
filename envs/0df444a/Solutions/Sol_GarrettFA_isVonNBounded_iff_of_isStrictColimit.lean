-- Prove2me | solution 1 for GarrettFA.isVonNBounded_iff_of_isStrictColimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:39:33.391738+00:00
-- url     : https://prove2.me/submissions/943282d6-b829-46f3-8914-428ee314978e

import Mathlib
import Definitions.Def_GarrettFA_IsStrictColimit

open Topology Set Filter Pointwise

namespace GAVNB

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]

lemma balancedCore_convex (W : Set V) (h0 : (0 : V) ∈ W) (hW : Convex ℝ W) :
    Convex ℝ (balancedCore 𝕜 W) := by
  rw [balancedCore_eq_iInter h0]
  refine convex_iInter fun r => convex_iInter fun _ => ?_
  intro x hx y hy a b ha hb hab
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨a • u + b • v, hW hu hv ha hb hab, ?_⟩
  simp only [smul_add]
  rw [← algebraMap_smul 𝕜 a (r • u), ← algebraMap_smul 𝕜 b (r • v), ← algebraMap_smul 𝕜 a u,
    ← algebraMap_smul 𝕜 b v, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm r, mul_comm r]

/-- the inductive invariant -/
def Good (F : ℕ → Submodule 𝕜 V) (n : ℕ) (U : Set V) : Prop :=
  U ⊆ F n ∧ Convex ℝ U ∧ Balanced 𝕜 U ∧ {y : F n | (y : V) ∈ U} ∈ 𝓝 (0 : F n)

lemma real_smul_eq (t : ℝ) (v : V) : t • v = ((t : 𝕜)) • v := by
  rw [← algebraMap_smul 𝕜 t v]

/-- extension step -/
lemma ext_step {F : ℕ → Submodule 𝕜 V} (hF : GarrettFA.IsStrictColimit 𝕜 F) (n : ℕ) (U : Set V)
    (hU : Good F n U) (P : Finset V) (hP : ∀ p ∈ P, p ∈ F (n + 1) ∧ p ∉ F n) :
    ∃ U' : Set V, Good F (n + 1) U' ∧ U ⊆ U' ∧ (∀ z ∈ U', z ∈ F n → z ∈ U) ∧ ∀ p ∈ P, p ∉ U' := by
  have hLC : LocallyConvexSpace ℝ V := hF.locallyConvex
  obtain ⟨hUF, hUc, hUb, hUn⟩ := hU
  have hmono : F n ≤ F (n + 1) := hF.strictMono.monotone (Nat.le_succ n)
  -- M : neighbourhood in V whose trace on F n lies in U
  rw [nhds_subtype, Filter.mem_comap] at hUn
  obtain ⟨M, hM, hMU⟩ := hUn
  have hM0 : M ∈ 𝓝 (0 : V) := by simpa using hM
  have hMU' : ∀ y ∈ F n, y ∈ M → y ∈ U := fun y hy hyM => hMU (show (⟨y, hy⟩ : F n) ∈ _ from hyM)
  -- for each p ∈ P a neighbourhood separating p from F n inside F (n+1)
  have hsep : ∀ p ∈ P, ∃ Mp ∈ 𝓝 (0 : V), ∀ z ∈ F (n + 1), z - p ∈ Mp → z ∉ F n := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hP p hp
    have hcl := hF.isClosed_in_succ n
    have hopen : {y : F (n + 1) | (y : V) ∉ F n} ∈ 𝓝 (⟨p, hp1⟩ : F (n + 1)) :=
      hcl.isOpen_compl.mem_nhds hp2
    rw [nhds_subtype, Filter.mem_comap] at hopen
    obtain ⟨Q, hQ, hQs⟩ := hopen
    refine ⟨(fun d => d + p) ⁻¹' Q, ?_, fun z hz hzp => ?_⟩
    · exact (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hQ)
    · have : (⟨z, hz⟩ : F (n + 1)) ∈ Subtype.val ⁻¹' Q := by simpa using hzp
      exact hQs this
  choose! Mp hMp hMpsep using hsep
  have hM1 : M ∩ ⋂ p ∈ P, Mp p ∈ 𝓝 (0 : V) :=
    inter_mem hM0 ((Filter.biInter_finset_mem P).mpr fun p hp => hMp p hp)
  obtain ⟨C, ⟨hC0, hCc⟩, hCsub⟩ := (LocallyConvexSpace.convex_basis_zero ℝ V).mem_iff.mp hM1
  set W := balancedCore 𝕜 C with hWdef
  have hW0 : W ∈ 𝓝 (0 : V) := balancedCore_mem_nhds_zero hC0
  have h0W : (0 : V) ∈ W := mem_of_mem_nhds hW0
  have hWc : Convex ℝ W := balancedCore_convex C (mem_of_mem_nhds hC0) hCc
  have hWb : Balanced 𝕜 W := balancedCore_balanced C
  have hWsub : W ⊆ M ∩ ⋂ p ∈ P, Mp p := (balancedCore_subset C).trans hCsub
  have h0U : (0 : V) ∈ U := hMU' 0 (F n).zero_mem (mem_of_mem_nhds hM0)
  set U' := convexJoin ℝ U W ∩ (F (n + 1) : Set V) with hU'def
  refine ⟨U', ⟨inter_subset_right, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hUc.convexJoin hWc).inter ((F (n + 1)).restrictScalars ℝ).convex
  · intro c hc
    rintro _ ⟨z, ⟨hzj, hzF⟩, rfl⟩
    refine ⟨?_, (F (n + 1)).smul_mem c hzF⟩
    rw [mem_convexJoin] at hzj ⊢
    obtain ⟨u, hu, w, hw, s, t, hs, ht, hst, rfl⟩ := hzj
    refine ⟨c • u, hUb.smul_mem hc hu, c • w, hWb.smul_mem hc hw, s, t, hs, ht, hst, ?_⟩
    show s • c • u + t • c • w = c • (s • u + t • w)
    rw [smul_add, smul_comm c s u, smul_comm c t w]
  · rw [nhds_subtype, Filter.mem_comap]
    refine ⟨W, by simpa using hW0, fun y hy => ⟨subset_convexJoin_right ⟨0, h0U⟩ hy, y.2⟩⟩
  · exact fun z hz => ⟨subset_convexJoin_left ⟨0, h0W⟩ hz, hmono (hUF hz)⟩
  · rintro z ⟨hzj, -⟩ hzn
    rw [mem_convexJoin] at hzj
    obtain ⟨u, hu, w, hw, s, t, hs, ht, hst, rfl⟩ := hzj
    rcases eq_or_lt_of_le ht with h | h
    · subst h
      have : s = 1 := by linarith
      subst this
      simpa using hu
    · have hwF : w ∈ F n := by
        have h1 : t • w = (s • u + t • w) - s • u := by abel
        have h2 : t • w ∈ F n := by
          rw [h1]; exact (F n).sub_mem hzn ((F n).smul_of_tower_mem s (hUF hu))
        have h3 : w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ h.ne', one_smul]
        rw [h3]; exact (F n).smul_of_tower_mem t⁻¹ h2
      have hwU : w ∈ U := hMU' w hwF (hWsub hw).1
      exact hUc hu hwU hs ht hst
  · intro p hp hpU
    obtain ⟨hzj, -⟩ := hpU
    rw [mem_convexJoin] at hzj
    obtain ⟨u, hu, w, hw, s, t, hs, ht, hst, hpe⟩ := hzj
    have hzF : s • u ∈ F n := (F n).smul_of_tower_mem s (hUF hu)
    have hdiff : s • u - p ∈ Mp p := by
      have : s • u - p = ((-t : ℝ) : 𝕜) • w := by
        rw [← hpe, ← real_smul_eq]; simp only [neg_smul]; abel
      rw [this]
      have hb : ‖((-t : ℝ) : 𝕜)‖ ≤ 1 := by
        rw [RCLike.norm_ofReal, abs_neg, abs_of_nonneg ht]; linarith
      have := hWsub (hWb.smul_mem hb hw)
      exact mem_iInter₂.mp this.2 p hp
    exact hMpsep p hp (s • u) (hmono hzF) hdiff hzF


/-- bounded sets lie in a single step -/
lemma bounded_in_step {F : ℕ → Submodule 𝕜 V} (hF : GarrettFA.IsStrictColimit 𝕜 F) (B : Set V)
    (hB : Bornology.IsVonNBounded 𝕜 B) : ∃ i, B ⊆ F i := by
  classical
  by_contra hcon
  push Not at hcon
  have hx : ∀ k, ∃ x ∈ B, x ∉ F k := fun k => not_subset.mp (hcon k)
  choose x hxB hxF using hx
  have hex : ∀ k, ∃ m, x k ∈ F m := fun k => hF.exists_mem (x k)
  let m : ℕ → ℕ := fun k => Nat.find (hex k)
  have hm : ∀ k, x k ∈ F (m k) := fun k => Nat.find_spec (hex k)
  have hmin : ∀ k j, j < m k → x k ∉ F j := fun k j hj => Nat.find_min (hex k) hj
  have hmono : Monotone F := hF.strictMono.monotone
  have hmk : ∀ k, k < m k := by
    intro k
    by_contra h
    push Not at h
    exact hxF k (hmono h (hm k))
  let y : ℕ → V := fun k => ((k + 1 : ℕ) : 𝕜)⁻¹ • x k
  have hc0 : ∀ k : ℕ, ((k + 1 : ℕ) : 𝕜) ≠ 0 := fun k => by exact_mod_cast Nat.succ_ne_zero k
  have hyx : ∀ k, x k = ((k + 1 : ℕ) : 𝕜) • y k := fun k => by
    simp only [y, smul_smul, mul_inv_cancel₀ (hc0 k), one_smul]
  have hyF : ∀ k j, y k ∈ F j ↔ x k ∈ F j := by
    intro k j
    constructor
    · intro h; rw [hyx k]; exact (F j).smul_mem _ h
    · intro h; exact (F j).smul_mem _ h
  let P : ℕ → Finset V := fun n => ((Finset.range n).filter (fun k => m k = n)).image y
  have hP : ∀ n, ∀ p ∈ P (n + 1), p ∈ F (n + 1) ∧ p ∉ F n := by
    intro n p hp
    simp only [P, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hp
    refine ⟨(hyF k _).mpr (hk ▸ hm k), fun h => hmin k n (by omega) ((hyF k n).mp h)⟩
  -- recursion
  have hbase : Good F 0 (F 0 : Set V) := by
    refine ⟨subset_rfl, ((F 0).restrictScalars ℝ).convex, fun c _ => ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩; exact (F 0).smul_mem c hz
    · convert univ_mem; ext y; simp
  let G : (n : ℕ) → {U : Set V // Good F n U} := fun n => Nat.rec ⟨(F 0 : Set V), hbase⟩
    (fun n G => ⟨Classical.choose (ext_step hF n G.1 G.2 (P (n + 1)) (hP n)),
      (Classical.choose_spec (ext_step hF n G.1 G.2 (P (n + 1)) (hP n))).1⟩) n
  have hGs : ∀ n, (G (n + 1)).1 = Classical.choose (ext_step hF n (G n).1 (G n).2 (P (n + 1)) (hP n)) :=
    fun n => rfl
  have hspec : ∀ n, (G n).1 ⊆ (G (n + 1)).1 ∧ (∀ z ∈ (G (n + 1)).1, z ∈ F n → z ∈ (G n).1) ∧
      ∀ p ∈ P (n + 1), p ∉ (G (n + 1)).1 := by
    intro n
    rw [hGs n]
    exact (Classical.choose_spec (ext_step hF n (G n).1 (G n).2 (P (n + 1)) (hP n))).2
  set Us : ℕ → Set V := fun n => (G n).1 with hUs
  have hUmono : Monotone Us := monotone_nat_of_le_succ fun n => (hspec n).1
  have htrace : ∀ n j, n ≤ j → ∀ z ∈ Us j, z ∈ F n → z ∈ Us n := by
    intro n j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun z hz _ => hz
    | succ j hnj ih =>
      intro z hz hzn
      exact ih z ((hspec j).2.1 z hz (hmono hnj hzn)) hzn
  set Uall := ⋃ n, Us n with hUall
  have hUc : Convex ℝ Uall := by
    intro a ha b hb s t hs ht hst
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    obtain ⟨j, hj⟩ := mem_iUnion.mp hb
    have hi' := hUmono (le_max_left i j) hi
    have hj' := hUmono (le_max_right i j) hj
    exact mem_iUnion.mpr ⟨max i j, (G (max i j)).2.2.1 hi' hj' hs ht hst⟩
  have hUb : Balanced 𝕜 Uall := by
    intro c hc
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i, (G i).2.2.2.1.smul_mem hc hi⟩
  have hUn : Uall ∈ 𝓝 (0 : V) := by
    apply hF.mem_nhds_of_absConvex Uall hUb hUc
    intro n
    exact mem_of_superset (G n).2.2.2.2 fun z hz => mem_iUnion.mpr ⟨n, hz⟩
  obtain ⟨r, -, hr⟩ := (hB hUn).exists_pos
  obtain ⟨k, hk⟩ := exists_nat_ge r
  have hsub := hr ((k + 1 : ℕ) : 𝕜) (by rw [RCLike.norm_natCast]; push_cast; linarith)
  obtain ⟨u, hu, hux⟩ := hsub (hxB k)
  have huy : u = y k := by
    have := hyx k
    rw [← hux] at this
    exact smul_right_injective V (hc0 k) this
  obtain ⟨n, hn⟩ : ∃ n, m k = n + 1 := ⟨m k - 1, by have := hmk k; omega⟩
  have hyP : y k ∈ P (n + 1) := by
    simp only [P, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨k, ⟨by have := hmk k; omega, hn⟩, rfl⟩
  have hyU : y k ∈ Us (n + 1) := by
    rw [← huy]
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    rcases le_total j (n + 1) with hjn | hjn
    · exact hUmono hjn hj
    · exact htrace (n + 1) j hjn u hj (by rw [huy, hyF, ← hn]; exact hm k)
  exact (hspec n).2.2 (y k) hyP hyU

end GAVNB

open GAVNB in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] {F : ℕ → Submodule 𝕜 V} (hF : GarrettFA.IsStrictColimit 𝕜 F)
    (B : Set V) :
    Bornology.IsVonNBounded 𝕜 B ↔
      ∃ i, B ⊆ F i ∧ Bornology.IsVonNBounded 𝕜 {y : F i | (y : V) ∈ B} := by
  constructor
  · intro hB
    obtain ⟨i, hi⟩ := bounded_in_step hF B hB
    refine ⟨i, hi, fun N hN => ?_⟩
    rw [nhds_subtype, Filter.mem_comap] at hN
    obtain ⟨M, hM, hMN⟩ := hN
    have hab := hB (by simpa using hM : M ∈ 𝓝 (0 : V))
    filter_upwards [hab, Bornology.eventually_ne_cobounded (0 : 𝕜)] with c hc hc0
    intro y hy
    obtain ⟨mm, hmm, hmy⟩ := hc hy
    have hmF : mm ∈ F i := by
      have : mm = c⁻¹ • (y : V) := by rw [← hmy, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]; exact (F i).smul_mem _ y.2
    refine ⟨⟨mm, hmF⟩, hMN (show (⟨mm, hmF⟩ : F i) ∈ Subtype.val ⁻¹' M from hmm), ?_⟩
    apply Subtype.ext
    simp [hmy]
  · rintro ⟨i, hi, hb⟩
    have := hb.image (F i).subtypeL
    have hs : B = (F i).subtypeL '' {y : F i | (y : V) ∈ B} := by
      ext z
      constructor
      · intro hz; exact ⟨⟨z, hi hz⟩, hz, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact hy
    rw [hs]; exact this
