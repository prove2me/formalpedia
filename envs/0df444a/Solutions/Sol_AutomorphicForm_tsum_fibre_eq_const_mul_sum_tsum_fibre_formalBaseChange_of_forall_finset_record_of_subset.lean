-- Prove2me | solution 1 for AutomorphicForm.tsum_fibre_eq_const_mul_sum_tsum_fibre_formalBaseChange_of_forall_finset_record_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a21db78d-5cfe-5ade-b4d9-3e634ea6c1e6

import Mathlib
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tsum_fibre_eq_const_mul_sum_tsum_fibre_formalBaseChange_of_forall_finset_record_of_subset

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped BigOperators NumberField
open Filter Topology

namespace W3GapLimit2

theorem tendsto_tsum_levelFibre {H : Type*} (C : Set H) (m : H → ℂ) (hm : Summable fun x : C => ‖m x‖)
    (F₀ : Finset ℕ) (P : ℕ → H → Prop) (Q : H → Prop) (hPQ : ∀ x ∈ C, m x ≠ 0 → ((∀ k, P k x) ↔ Q x)) :
    Tendsto (fun n => ∑' x : {x : H // x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x}, m x.1) atTop
      (𝓝 (∑' x : {x : H // x ∈ C ∧ Q x}, m x.1)) := by
  classical
  have e1 : ∀ n, (∑' x : {x : H // x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x}, m x.1) =
      ∑' x : H, Set.indicator {x : H | x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x} m x :=
    fun n => tsum_subtype {x : H | x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x} m
  have e2 : (∑' x : {x : H // x ∈ C ∧ Q x}, m x.1) = ∑' x : H, Set.indicator {x : H | x ∈ C ∧ Q x} m x :=
    tsum_subtype {x : H | x ∈ C ∧ Q x} m
  rw [e2, show (fun n => ∑' x : {x : H // x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x}, m x.1) =
      fun n => ∑' x : H, Set.indicator {x : H | x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x} m x from funext e1]
  have hbound : Summable (C.indicator fun x => ‖m x‖) := summable_subtype_iff_indicator.mp hm
  refine tendsto_tsum_of_dominated_convergence (bound := C.indicator fun x => ‖m x‖) hbound ?_
    (Eventually.of_forall fun n x => ?_)
  · intro x
    by_cases hx : x ∈ C
    · by_cases hm0 : m x = 0
      · have h0 : ∀ s : Set H, s.indicator m x = 0 := fun s => by
          by_cases hs : x ∈ s
          · rw [Set.indicator_of_mem hs, hm0]
          · rw [Set.indicator_of_notMem hs]
        simp only [h0]
        exact tendsto_const_nhds
      · by_cases hQ : Q x
        · have hall : ∀ k, P k x := (hPQ x hx hm0).mpr hQ
          rw [Set.indicator_of_mem (show x ∈ {x : H | x ∈ C ∧ Q x} from ⟨hx, hQ⟩)]
          refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
          exact Set.indicator_of_mem (show x ∈ {x : H | x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x} from
            ⟨hx, fun k _ => hall k⟩) m
        · have hnall : ¬ ∀ k, P k x := fun h => hQ ((hPQ x hx hm0).mp h)
          push Not at hnall
          obtain ⟨k₀, hk₀⟩ := hnall
          rw [Set.indicator_of_notMem (show x ∉ {x : H | x ∈ C ∧ Q x} from fun h => hQ h.2)]
          refine tendsto_atTop_of_eventually_const (i₀ := k₀ + 1) fun n hn => ?_
          exact Set.indicator_of_notMem (show x ∉ {x : H | x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x} from
            fun h => hk₀ (h.2 k₀ (Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))))) m
    · have h0 : ∀ (R : H → Prop), Set.indicator {x : H | x ∈ C ∧ R x} m x = 0 := fun R =>
        Set.indicator_of_notMem (fun h => hx h.1) m
      simp only [h0]
      exact tendsto_const_nhds
  · by_cases hxs : x ∈ {x : H | x ∈ C ∧ ∀ k ∈ F₀ ∪ Finset.range n, P k x}
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs.1]
    · rw [Set.indicator_of_notMem hxs, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) x

end W3GapLimit2

open W3GapLimit2 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (rec : ℕ → HeightOneSpectrum (𝓞 L)) (hrec : ∀ k, rec k ∉ SL)
    (hcov : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      ∃ k, HeightOneSpectrum.under (𝓞 K) (rec k) = HeightOneSpectrum.under (𝓞 K) w)
    (CL : Set (HeckeEigensystem L ℂ)) (mL : HeckeEigensystem L ℂ → ℂ)
    (hmL : Summable fun Ψ : CL => ‖mL Ψ‖)
    (hL : ∀ Ψ ∈ CL, mL Ψ ≠ 0 → ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (Ψ.a w, Ψ.b w) = (Ψ.a w', Ψ.b w'))
    {ΞT : Type} (Ξ : Finset ΞT) (CK : ΞT → Set (HeckeEigensystem K ℂ)) (mK : ΞT → HeckeEigensystem K ℂ → ℂ)
    (hmK : ∀ ξ ∈ Ξ, Summable fun π : CK ξ => ‖mK ξ π‖)
    (hK : ∀ ξ ∈ Ξ, ∀ π ∈ CK ξ, mK ξ π ≠ 0 → ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) =
          ((formalBaseChange K L π).a w', (formalBaseChange K L π).b w'))
    (t : HeightOneSpectrum (𝓞 L) → ℂ × ℂ)
    (ht : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → t w = t w')
    (E : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (e : ℕ → ℂ) (he : Summable fun n => ‖e n‖)
    (hE : ∀ n, e n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → E n w = E n w') ∧
        ∃ w : HeightOneSpectrum (𝓞 L), w ∉ SL ∧ t w ≠ E n w)
    (bandL bandK c₀ : ℂ) (hbandL : bandL ≠ 0) (F₀ : Finset ℕ)
    (hlevel : ∀ F : Finset ℕ, F₀ ⊆ F →
      bandL * (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ CL ∧ ∀ k ∈ F, (Ψ.a (rec k), Ψ.b (rec k)) = t (rec k)}, mL Ψ.1) -
        c₀ * bandK * (∑ ξ ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
            ∀ k ∈ F, ((formalBaseChange K L π).a (rec k), (formalBaseChange K L π).b (rec k)) = t (rec k)},
          mK ξ π.1) +
        (∑' n : {n : ℕ // ∀ k ∈ F, E n (rec k) = t (rec k)}, e n.1) = 0) :
    (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ CL ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → (Ψ.a w, Ψ.b w) = t w}, mL Ψ.1) =
      c₀ * bandK / bandL * ∑ ξ ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) = t w}, mK ξ π.1 := by
  classical

  have hgapL : ∀ Ψ ∈ CL, mL Ψ ≠ 0 →
      ((∀ k, (Ψ.a (rec k), Ψ.b (rec k)) = t (rec k)) ↔
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → (Ψ.a w, Ψ.b w) = t w) := by
    intro Ψ hΨ hm
    constructor
    · intro h w hw
      obtain ⟨k, hk⟩ := hcov w hw
      rw [← hL Ψ hΨ hm (rec k) w (hrec k) hw hk, ← ht (rec k) w (hrec k) hw hk]
      exact h k
    · intro h k
      exact h (rec k) (hrec k)

  have hgapK : ∀ ξ ∈ Ξ, ∀ π ∈ CK ξ, mK ξ π ≠ 0 →
      ((∀ k, ((formalBaseChange K L π).a (rec k), (formalBaseChange K L π).b (rec k)) = t (rec k)) ↔
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) = t w) := by
    intro ξ hξ π hπ hm
    constructor
    · intro h w hw
      obtain ⟨k, hk⟩ := hcov w hw
      rw [← hK ξ hξ π hπ hm (rec k) w (hrec k) hw hk, ← ht (rec k) w (hrec k) hw hk]
      exact h k
    · intro h k
      exact h (rec k) (hrec k)

  have hgapE : ∀ n ∈ (Set.univ : Set ℕ), e n ≠ 0 → ((∀ k, E n (rec k) = t (rec k)) ↔ False) := by
    intro n _ hn
    obtain ⟨hconst, w, hw, hne⟩ := hE n hn
    constructor
    · intro h
      obtain ⟨k, hk⟩ := hcov w hw
      apply hne
      rw [← ht (rec k) w (hrec k) hw hk, ← hconst (rec k) w (hrec k) hw hk]
      exact (h k).symm
    · intro h; exact h.elim

  have hA := tendsto_tsum_levelFibre CL mL hmL F₀ (fun k Ψ => (Ψ.a (rec k), Ψ.b (rec k)) = t (rec k))
    (fun Ψ => ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → (Ψ.a w, Ψ.b w) = t w) hgapL
  have hB : ∀ ξ ∈ Ξ, Tendsto (fun n => ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
      ∀ k ∈ F₀ ∪ Finset.range n, ((formalBaseChange K L π).a (rec k), (formalBaseChange K L π).b (rec k)) = t (rec k)},
        mK ξ π.1) atTop
      (𝓝 (∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) = t w}, mK ξ π.1)) :=
    fun ξ hξ => tendsto_tsum_levelFibre (CK ξ) (mK ξ) (hmK ξ hξ) F₀
      (fun k π => ((formalBaseChange K L π).a (rec k), (formalBaseChange K L π).b (rec k)) = t (rec k))
      (fun π => ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) = t w) (hgapK ξ hξ)
  have heU : Summable fun n : (Set.univ : Set ℕ) => ‖e n‖ := he.comp_injective Subtype.val_injective
  have hC := tendsto_tsum_levelFibre (Set.univ : Set ℕ) e heU F₀ (fun k n => E n (rec k) = t (rec k))
    (fun _ => False) hgapE

  have eE : ∀ F : Finset ℕ, (∑' n : {n : ℕ // n ∈ (Set.univ : Set ℕ) ∧ ∀ k ∈ F, E n (rec k) = t (rec k)}, e n.1) =
      ∑' n : {n : ℕ // ∀ k ∈ F, E n (rec k) = t (rec k)}, e n.1 := by
    intro F
    rw [show (∑' n : {n : ℕ // n ∈ (Set.univ : Set ℕ) ∧ ∀ k ∈ F, E n (rec k) = t (rec k)}, e n.1) =
        ∑' n, Set.indicator {n : ℕ | n ∈ (Set.univ : Set ℕ) ∧ ∀ k ∈ F, E n (rec k) = t (rec k)} e n from
        tsum_subtype _ e,
      show (∑' n : {n : ℕ // ∀ k ∈ F, E n (rec k) = t (rec k)}, e n.1) =
        ∑' n, Set.indicator {n : ℕ | ∀ k ∈ F, E n (rec k) = t (rec k)} e n from tsum_subtype _ e]
    have hs : {n : ℕ | n ∈ (Set.univ : Set ℕ) ∧ ∀ k ∈ F, E n (rec k) = t (rec k)} =
        {n : ℕ | ∀ k ∈ F, E n (rec k) = t (rec k)} := by ext n; simp
    rw [hs]
  have e0 : (∑' n : {n : ℕ // n ∈ (Set.univ : Set ℕ) ∧ False}, e n.1) = 0 := by
    rw [show (∑' n : {n : ℕ // n ∈ (Set.univ : Set ℕ) ∧ False}, e n.1) =
        ∑' n, Set.indicator {n : ℕ | n ∈ (Set.univ : Set ℕ) ∧ False} e n from tsum_subtype _ e]
    have hs : {n : ℕ | n ∈ (Set.univ : Set ℕ) ∧ False} = ∅ := by ext n; simp
    rw [hs, Set.indicator_empty]
    exact tsum_zero
  have hC' : Tendsto (fun n => ∑' m : {m : ℕ // ∀ k ∈ F₀ ∪ Finset.range n, E m (rec k) = t (rec k)}, e m.1)
      atTop (𝓝 0) := by
    rw [← e0]
    exact hC.congr fun n => eE (F₀ ∪ Finset.range n)
  have hsum := tendsto_finsetSum Ξ fun ξ hξ => hB ξ hξ
  have hcomb := ((hA.const_mul bandL).sub (hsum.const_mul (c₀ * bandK))).add hC'
  have hzero : (fun n => bandL * (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ CL ∧
      ∀ k ∈ F₀ ∪ Finset.range n, (Ψ.a (rec k), Ψ.b (rec k)) = t (rec k)}, mL Ψ.1) -
        c₀ * bandK * (∑ ξ ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
            ∀ k ∈ F₀ ∪ Finset.range n, ((formalBaseChange K L π).a (rec k), (formalBaseChange K L π).b (rec k)) =
              t (rec k)}, mK ξ π.1) +
        (∑' m : {m : ℕ // ∀ k ∈ F₀ ∪ Finset.range n, E m (rec k) = t (rec k)}, e m.1)) = fun _ => 0 :=
    funext fun n => hlevel (F₀ ∪ Finset.range n) Finset.subset_union_left
  rw [hzero] at hcomb
  have hlim := tendsto_nhds_unique tendsto_const_nhds hcomb
  beta_reduce at hlim
  rw [div_mul_eq_mul_div, eq_div_iff hbandL]
  linear_combination -hlim

#print axioms solution

end S_AutomorphicForm_tsum_fibre_eq_const_mul_sum_tsum_fibre_formalBaseChange_of_forall_finset_record_of_subset
end P2MW
export P2MW.S_AutomorphicForm_tsum_fibre_eq_const_mul_sum_tsum_fibre_formalBaseChange_of_forall_finset_record_of_subset (solution)
