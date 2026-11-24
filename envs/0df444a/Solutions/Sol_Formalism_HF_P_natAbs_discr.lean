-- Prove2me | solution 1 for Formalism.HF.P.natAbs_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:23:58.611471+00:00
-- url     : https://prove2.me/submissions/916f19d9-bcf0-477d-9552-00b21fbf7f4c

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Theorems.Thm_Formalism_HF_P_not_isSquare_prod
import Theorems.Thm_Formalism_HF_P_adjoin_top_of_lift
import Theorems.Thm_Formalism_HF_P_sqf_neg
import Theorems.Thm_Formalism_Q3_mqGalois
import Theorems.Thm_Formalism_Q3_mqKummer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (hQ : QuadDiscr) : ∀ (m : ℕ) (q : Fin (m + 1) → ℕ),
    (∀ i, (q i).Prime ∧ q i % 4 = 3) → Function.Injective q →
    ∀ (E : Type) [Field E] [NumberField E] (α : Fin (m + 1) → E),
      IsMQ (fun i => -(q i : ℤ)) α → (discr E).natAbs = ∏ i, q i ^ (2 ^ m) := by
  intro m
  induction m with
  | zero =>
    intro q hq hinj E _ _ α hMQ
    have htop : adjoin ℚ {α 0} = ⊤ := by
      have hr : Set.range α = {α 0} := by
        ext x
        exact ⟨fun ⟨i, hi⟩ => by rw [← hi, Fin.fin_one_eq_zero i]; rfl, fun h => ⟨0, h.symm⟩⟩
      rw [← hr]
      exact hMQ.2
    have h := hQ E (-(q 0 : ℤ)) (α 0) (hMQ.1 0) htop (sqf_neg _ (hq 0).1)
      (by have := (hq 0).2; omega)
    rw [h]
    simp
  | succ m ih =>
    intro q hq hinj E _ _ α hMQ
    classical
    set K₁ : IntermediateField ℚ E :=
      adjoin ℚ (Set.range (fun i : Fin (m + 1) => α i.castSucc)) with hK₁
    set K₂ : IntermediateField ℚ E := adjoin ℚ {α (Fin.last (m + 1))} with hK₂
    let β : Fin (m + 1) → K₁ := fun i => ⟨α i.castSucc, subset_adjoin _ _ ⟨i, rfl⟩⟩
    let γ : K₂ := ⟨α (Fin.last _), mem_adjoin_simple_self _ _⟩
    have hβ : IsMQ (fun i => -(q i.castSucc : ℤ)) β := by
      refine ⟨fun i => Subtype.ext (by simpa using hMQ.1 i.castSucc), ?_⟩
      apply adjoin_top_of_lift
      rw [← Set.range_comp]
      rfl
    have hγsq : γ ^ 2 = ((-(q (Fin.last _) : ℤ) : ℤ) : K₂) :=
      Subtype.ext (by simpa using hMQ.1 (Fin.last _))
    have hγtop : adjoin ℚ {γ} = ⊤ := by
      apply adjoin_top_of_lift
      rw [Set.image_singleton]
    have hq' : ∀ i : Fin (m + 1), (q i.castSucc).Prime ∧ q i.castSucc % 4 = 3 := fun i => hq _
    have hinj' : Function.Injective (fun i : Fin (m + 1) => q i.castSucc) :=
      hinj.comp (Fin.castSucc_injective _)
    have hd₁ := ih (fun i => q i.castSucc) hq' hinj' K₁ β hβ
    have hd₂ : discr K₂ = -(q (Fin.last _) : ℤ) :=
      hQ K₂ _ γ hγsq hγtop (sqf_neg _ (hq _).1) (by have := (hq (Fin.last _)).2; omega)
    have hf₁ : Module.finrank ℚ K₁ = 2 ^ (m + 1) :=
      (mqKummer (m + 1) K₁ _ β hβ
        (not_isSquare_prod _ (fun i => (hq' i).1) hinj')).1
    have hγMQ : IsMQ (fun _ : Fin 1 => -(q (Fin.last (m + 1)) : ℤ)) (fun _ => γ) := by
      refine ⟨fun _ => hγsq, ?_⟩
      rw [Set.range_const]
      exact hγtop
    have hf₂ : Module.finrank ℚ K₂ = 2 :=
      (mqKummer 1 K₂ _ (fun _ => γ) hγMQ
        (not_isSquare_prod (fun _ : Fin 1 => q (Fin.last (m + 1))) (fun _ => (hq _).1)
          (fun a b _ => Subsingleton.elim a b))).1
    have : IsGalois ℚ K₁ := (mqGalois _ K₁ _ β hβ
      (fun i => neg_ne_zero.2 (Nat.cast_ne_zero.2 (hq' i).1.ne_zero))).1
    have hcop : IsCoprime (discr K₁) (discr K₂) := by
      rw [hd₂, IsCoprime.neg_right_iff, isCoprime_comm]
      have hp : Prime (q (Fin.last _) : ℤ) := Nat.prime_iff_prime_int.1 (hq _).1
      rw [Prime.coprime_iff_not_dvd hp, Int.natCast_dvd, hd₁]
      intro hdvd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (hq (Fin.last _)).1.prime _).1 hdvd
      have h1 := (hq (Fin.last _)).1.dvd_of_dvd_pow hi
      have h2 := (Nat.prime_dvd_prime_iff_eq (hq (Fin.last _)).1 (hq' i).1).1 h1
      exact (Fin.castSucc_lt_last i).ne (hinj h2).symm
    have hld := linearDisjoint_of_isGalois_isCoprime_discr E K₁ K₂ hcop
    have hsup : K₁ ⊔ K₂ = ⊤ := by
      rw [hK₁, hK₂, ← adjoin_union]
      convert hMQ.2 using 2
      ext x
      simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro (⟨i, rfl⟩ | rfl) <;> exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        induction i using Fin.lastCases with
        | last => exact Or.inr rfl
        | cast j => exact Or.inl ⟨j, rfl⟩
    have hnat := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow E K₁ K₂ hld hsup
      (isCoprime_differentIdeal_of_isCoprime_discr E hcop)
    rw [hnat, hd₁, hd₂, hf₁, hf₂,
      Fin.prod_univ_castSucc (n := m + 1) (f := fun i => q i ^ 2 ^ (m + 1)), ← Finset.prod_pow]
    simp only [← pow_mul, Int.natAbs_neg, Int.natAbs_natCast]
    congr 1
end Formalism.HF.P
