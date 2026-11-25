-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.leadingTermLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:24.532559+00:00
-- url     : https://prove2.me/submissions/72a565ab-bb13-4390-8d2b-3e99888de8db

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_GradedFreeLengthFiltered
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LeadingTermLength
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_filteredLength


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LeadingTermLength := by
  intro O A A0 _ _ _ _ _ n F ι _ _ deg δ t σ u h0 hn hF hker hsurj hdeg hu hli
  classical
  have hanti : Antitone F := antitone_nat_of_succ_le hF
  have hkill : ∀ k (x : A) (h : x ∈ F k), x ∈ F (k + 1) → σ k ⟨x, h⟩ = 0 := by
    intro k x h hx
    have : (⟨x, h⟩ : ↥(F k)) ∈ LinearMap.ker (σ k) := by
      rw [hker k]; exact hx
    exact this
  have hkill' : ∀ k (x : A) (h : x ∈ F k), σ k ⟨x, h⟩ = 0 → x ∈ F (k + 1) := by
    intro k x h hx
    have : (⟨x, h⟩ : ↥(F k)) ∈ LinearMap.ker (σ k) := hx
    rw [hker k] at this
    exact this

  have hmem0 : ∀ (α : ι) (j : ℕ) (a : Fin δ → O), (deg α < j → a = 0) →
      ∑ i, a i • u α i ∈ F j := by
    intro α j a ha
    rcases lt_or_ge (deg α) j with h | h
    · rw [ha h]; simp
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hanti h (hu α i).1)
  have hval0 : ∀ (α : ι) (j : ℕ) (a : Fin δ → O) (h : ∑ i, a i • u α i ∈ F j),
      (deg α < j → a = 0) → ∀ β : {β : ι // deg β = j},
        σ j ⟨∑ i, a i • u α i, h⟩ β = if β.1 = α then ∑ i, a i • t i else 0 := by
    intro α j a h ha β
    rcases lt_trichotomy (deg α) j with hlt | heq | hgt
    · have hz : (⟨∑ i, a i • u α i, h⟩ : ↥(F j)) = 0 := by
        apply Subtype.ext
        simp [ha hlt]
      rw [hz, ha hlt]; simp
    · subst heq
      have hz : (⟨∑ i, a i • u α i, h⟩ : ↥(F (deg α))) =
          ∑ i, a i • (⟨u α i, (hu α i).1⟩ : ↥(F (deg α))) := by
        apply Subtype.ext
        simp
      rw [hz, map_sum, Finset.sum_apply]
      have : ∀ i, (σ (deg α)) (a i • (⟨u α i, (hu α i).1⟩ : ↥(F (deg α)))) β =
          if β.1 = α then a i • t i else 0 := by
        intro i
        rw [map_smul, (hu α i).2, Pi.smul_apply, Pi.single_apply]
        by_cases hb : β.1 = α
        · have : β = ⟨α, rfl⟩ := Subtype.ext hb
          simp [this]
        · have : β ≠ ⟨α, rfl⟩ := fun h' => hb (congrArg Subtype.val h')
          simp [this, hb]
      simp_rw [this]
      by_cases hb : β.1 = α <;> simp [hb]
    · have hx : ∑ i, a i • u α i ∈ F (j + 1) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hanti hgt (hu α i).1)
      rw [hkill j _ h hx]
      have hb : β.1 ≠ α := by
        intro hb
        have := β.2
        rw [hb] at this
        omega
      simp [hb]

  have hmem1 : ∀ (j : ℕ) (c : ι → Fin δ → O), (∀ α, deg α < j → c α = 0) →
      ∑ α, ∑ i, c α i • u α i ∈ F j := fun j c hc =>
    Submodule.sum_mem _ fun α _ => hmem0 α j (c α) (hc α)
  have hval1 : ∀ (j : ℕ) (c : ι → Fin δ → O) (h : ∑ α, ∑ i, c α i • u α i ∈ F j),
      (∀ α, deg α < j → c α = 0) → ∀ β : {β : ι // deg β = j},
        σ j ⟨∑ α, ∑ i, c α i • u α i, h⟩ β = ∑ i, c β.1 i • t i := by
    intro j c h hc β
    have hz : (⟨∑ α, ∑ i, c α i • u α i, h⟩ : ↥(F j)) =
        ∑ α, (⟨∑ i, c α i • u α i, hmem0 α j (c α) (hc α)⟩ : ↥(F j)) := by
      apply Subtype.ext
      simp
    rw [hz, map_sum, Finset.sum_apply]
    simp_rw [hval0 _ j _ _ (hc _) β]
    simp

  have hstrict : ∀ (k : ℕ) (c : ι → Fin δ → O), ∑ α, ∑ i, c α i • u α i ∈ F k →
      ∀ j, j ≤ k → ∀ α, deg α < j → c α = 0 := by
    intro k c hb j
    induction j with
    | zero => intro _ α h; omega
    | succ j ih =>
      intro hj α hα
      have ih' := ih (by omega)
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hα) with h | h
      · exact ih' α h
      · have hbj := hmem1 j c ih'
        have h1 := hval1 j c hbj ih' ⟨α, h⟩
        rw [hkill j _ hbj (hanti hj hb)] at h1
        funext i
        exact Fintype.linearIndependent_iff.mp hli (c α) h1.symm i
  set N : Submodule O A := Submodule.span O (Set.range fun p : ι × Fin δ => u p.1 p.2) with hN
  have hNmem : ∀ x : A, x ∈ N ↔ ∃ c : ι → Fin δ → O, ∑ α, ∑ i, c α i • u α i = x := by
    intro x
    rw [hN, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun α i => c (α, i), by rw [Fintype.sum_prod_type]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨fun p => c p.1 p.2, by rw [Fintype.sum_prod_type]⟩
  set T : Submodule O A0 := Submodule.span O (Set.range t) with hT

  have hgr : ∀ k, (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype =
      (Submodule.pi Set.univ fun _ : {α : ι // deg α = k} => T).comap (σ k) := by
    intro k
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · intro h β
      obtain ⟨a, ha, b, ⟨hbN, hbF⟩, rfl⟩ := Submodule.mem_sup.mp h
      obtain ⟨c, rfl⟩ := (hNmem b).mp hbN
      have hc := hstrict k c hbF k le_rfl
      have hz : (⟨a + ∑ α, ∑ i, c α i • u α i, hx⟩ : ↥(F k)) =
          ⟨a, hF k ha⟩ + ⟨∑ α, ∑ i, c α i • u α i, hbF⟩ := rfl
      rw [hz, map_add, hkill k a _ ha, zero_add, hval1 k c hbF hc β]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro h
      have hch : ∀ β : {α : ι // deg α = k}, ∃ a : Fin δ → O, ∑ i, a i • t i = σ k ⟨x, hx⟩ β :=
        fun β => (Submodule.mem_span_range_iff_exists_fun O).mp (h β)
      choose a ha using hch
      let c : ι → Fin δ → O := fun α => if hα : deg α = k then a ⟨α, hα⟩ else 0
      have hc : ∀ α, deg α < k → c α = 0 := by
        intro α hα
        simp only [c]
        rw [dif_neg (by omega)]
      have hyF := hmem1 k c hc
      have hyN : ∑ α, ∑ i, c α i • u α i ∈ N := (hNmem _).mpr ⟨c, rfl⟩
      have hσ : σ k ⟨x, hx⟩ = σ k ⟨∑ α, ∑ i, c α i • u α i, hyF⟩ := by
        funext β
        rw [hval1 k c hyF hc β, ← ha β]
        simp only [c]
        rw [dif_pos β.2]
      have hd : x - ∑ α, ∑ i, c α i • u α i ∈ F (k + 1) := by
        refine hkill' k _ ((F k).sub_mem hx hyF) ?_
        have hz : (⟨x - ∑ α, ∑ i, c α i • u α i, (F k).sub_mem hx hyF⟩ : ↥(F k)) =
            ⟨x, hx⟩ - ⟨∑ α, ∑ i, c α i • u α i, hyF⟩ := rfl
        rw [hz, map_sub, hσ, sub_self]
      refine Submodule.mem_sup.mpr ⟨_, hd, _, ⟨hyN, hyF⟩, by abel⟩
  have hlen : ∀ k, Module.length O (↥(F k) ⧸ (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype) =
      (Fintype.card {α : ι // deg α = k} : ℕ∞) * Module.length O (A0 ⧸ T) := by
    intro k
    set P : Submodule O ({α : ι // deg α = k} → A0) :=
      Submodule.pi Set.univ fun _ : {α : ι // deg α = k} => T with hP
    have hk : LinearMap.ker (P.mkQ ∘ₗ σ k) = (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, hgr k]
    have hs : Function.Surjective (P.mkQ ∘ₗ σ k) :=
      (Submodule.mkQ_surjective P).comp (hsurj k)
    have e1 := (Submodule.quotEquivOfEq _ _ hk).symm.trans
      ((P.mkQ ∘ₗ σ k).quotKerEquivOfSurjective hs)
    have e2 := Submodule.quotientPi (fun _ : {α : ι // deg α = k} => T)
    rw [e1.length_eq, e2.length_eq, Module.length_pi_of_fintype]
    simp
  rw [filteredLength O A n F h0 hn hF N]
  simp_rw [hlen]
  rw [← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι)) (t := Finset.range n)
    (f := deg) (fun α _ => by simpa using hdeg α)
  rw [Finset.card_univ] at this
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_subtype]
end Formalism.LatticeBaseChangeAlt
