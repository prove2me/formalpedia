-- Prove2me | solution 1 for DSDensity1246.Main.density_le_ds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:20:38.806377+00:00
-- url     : https://prove2.me/submissions/6317fb04-d9bf-44c4-a823-6531b47da4eb

import Mathlib
import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_maximumDensity
import Definitions.Def_DSDensity1246_Main_monomials
import Theorems.Thm_DSDensity1246_Main_spanning_lemma

section
namespace DSDensity1246.Dev.Density
open DSDensity1246.Main

theorem mem_finiteFiber {Y : Type*} {n : ℕ} (W : Finset (Fin n → Y)) (i : Fin n)
    (a : {j : Fin n // j ≠ i} → Y) (w : Fin n → Y) :
    w ∈ finiteFiber W i a ↔ w ∈ W ∧ away i w = a := by
  unfold finiteFiber
  simp [Finset.mem_filter]

theorem mem_finiteBehaviors {Y : Type*} {n : ℕ} (W : Finset (Fin n → Y)) (i : Fin n)
    (a : {j : Fin n // j ≠ i} → Y) :
    a ∈ finiteBehaviors W i ↔ ∃ w ∈ W, away i w = a := by
  unfold finiteBehaviors
  simp [Finset.mem_image]

theorem per_dir {Y : Type*} {n : ℕ} (ℓ : ℕ) (W : Finset (Fin n → Y)) (lam : Y → ℝ)
    (i : Fin n) {ι : Type*} [Fintype ι] (b : ι → (↥W → ℝ))
    (hli : LinearIndependent ℝ b) (α : ι → Fin n → ℕ)
    (hb : ∀ x (w : ↥W), b x w = ∏ j, lam (w.1 j) ^ α x j) :
    (Finset.univ.filter (fun x => α x i < ℓ)).card ≤
      ∑ a ∈ finiteBehaviors W i, min (finiteFiber W i a).card ℓ := by
  classical
  let A := finiteBehaviors W i
  let E : A → Finset (Fin n → Y) := fun a => finiteFiber W i a.1
  let Lm : (a : A) → Polynomial ℝ →ₗ[ℝ] (E a → ℝ) := fun a =>
    LinearMap.pi (fun w : E a => Polynomial.leval (lam (w.1 i)))
  let R : (a : A) → Submodule ℝ (E a → ℝ) := fun a =>
    (Polynomial.degreeLT ℝ ℓ).map (Lm a)
  let Ψ : ((a : A) → R a) →ₗ[ℝ] ((a : A) → (E a → ℝ)) :=
    LinearMap.pi (fun a => (R a).subtype ∘ₗ LinearMap.proj a)
  have hmemE : ∀ (a : A) (w : E a), w.1 ∈ W := fun a w =>
    ((mem_finiteFiber W i a.1 w.1).1 w.2).1
  let ρ : (↥W → ℝ) →ₗ[ℝ] ((a : A) → (E a → ℝ)) :=
    LinearMap.pi (fun a => LinearMap.funLeft ℝ ℝ (fun w : E a => (⟨w.1, hmemE a w⟩ : ↥W)))
  have hρ : Function.Injective ρ := by
    intro f g h
    funext ⟨w, hw⟩
    have hA : away i w ∈ A := (mem_finiteBehaviors W i _).2 ⟨w, hw, rfl⟩
    have hwE : w ∈ finiteFiber W i (away i w) := (mem_finiteFiber _ _ _ _).2 ⟨hw, rfl⟩
    have := congrFun (congrFun h ⟨away i w, hA⟩) ⟨w, hwE⟩
    simpa [ρ] using this
  let J := {x : ι // α x i < ℓ}
  let y : J → ((a : A) → (E a → ℝ)) := fun j => ρ (b j.1)
  have hy : LinearIndependent ℝ y :=
    (hli.comp Subtype.val Subtype.val_injective).map' ρ (LinearMap.ker_eq_bot.2 hρ)
  have hyr : ∀ j : J, y j ∈ LinearMap.range Ψ := by
    intro j
    let c : A → ℝ := fun a => ∏ t : {t : Fin n // t ≠ i}, lam (a.1 t) ^ α j.1 t.1
    have hdeg : ∀ a : A, (Polynomial.C (c a) * Polynomial.X ^ (α j.1 i)) ∈
        Polynomial.degreeLT ℝ ℓ := by
      intro a
      rw [Polynomial.mem_degreeLT]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast j.2
    refine ⟨fun a => ⟨Lm a (Polynomial.C (c a) * Polynomial.X ^ (α j.1 i)),
      Submodule.mem_map_of_mem (hdeg a)⟩, ?_⟩
    funext a w
    have hw : away i w.1 = a.1 := ((mem_finiteFiber W i a.1 w.1).1 w.2).2
    have h1 := hb j.1 ⟨w.1, hmemE a w⟩
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i] at h1
    have h2 : ∏ t : {t : Fin n // t ≠ i}, lam (w.1 t.1) ^ α j.1 t.1 = c a := by
      apply Finset.prod_congr rfl
      intro t _
      have := congrFun hw t
      simp only [away] at this
      rw [this]
    rw [h2] at h1
    simp only [Ψ, y, ρ, Lm, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearMap.proj_apply, LinearMap.funLeft_apply,
      Polynomial.leval_apply, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [h1]
    ring
  have hcard : Fintype.card J ≤ Module.finrank ℝ (LinearMap.range Ψ) := by
    rw [← finrank_span_eq_card hy]
    apply Submodule.finrank_mono
    exact Submodule.span_le.2 (Set.range_subset_iff.2 hyr)
  have hR : ∀ a : A, Module.finrank ℝ (R a) ≤ min (finiteFiber W i a.1).card ℓ := by
    intro a
    refine le_min ?_ ?_
    · calc Module.finrank ℝ (R a) ≤ Module.finrank ℝ (E a → ℝ) := Submodule.finrank_le _
        _ = _ := by simp [E]
    · calc Module.finrank ℝ (R a) ≤ Module.finrank ℝ (Polynomial.degreeLT ℝ ℓ) :=
            Submodule.finrank_map_le _ _
        _ = ℓ := by
          rw [(Polynomial.degreeLTEquiv ℝ ℓ).finrank_eq]; simp
  calc (Finset.univ.filter (fun x => α x i < ℓ)).card = Fintype.card J :=
        (Fintype.card_subtype _).symm
    _ ≤ Module.finrank ℝ (LinearMap.range Ψ) := hcard
    _ ≤ Module.finrank ℝ ((a : A) → R a) := LinearMap.finrank_range_le _
    _ = ∑ a : A, Module.finrank ℝ (R a) := Module.finrank_pi_fintype ℝ
    _ ≤ ∑ a : A, min (finiteFiber W i a.1).card ℓ := Finset.sum_le_sum (fun a _ => hR a)
    _ = _ := Finset.sum_coe_sort A (fun a => min (finiteFiber W i a).card ℓ)


theorem core {Y : Type*} {n : ℕ} (ℓ d : ℕ) (W : Finset (Fin n → Y)) (lam : Y → ℝ)
    (hspan : Submodule.span ℝ {f : ↥W → ℝ | ∃ α : Fin n → ℕ,
      (Finset.univ.filter (fun i => ℓ ≤ α i)).card ≤ d ∧
        f = fun w => ∏ i, lam (w.1 i) ^ α i} = ⊤) :
    ∑ i : Fin n, ∑ a ∈ finiteBehaviors W i, ((finiteFiber W i a).card - ℓ) ≤ d * W.card := by
  classical
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℝ
    {f : ↥W → ℝ | ∃ α : Fin n → ℕ,
      (Finset.univ.filter (fun i => ℓ ≤ α i)).card ≤ d ∧
        f = fun w => ∏ i, lam (w.1 i) ^ α i}
  have : Finite b := hbli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcardb : Fintype.card b = W.card := by
    have h1 := finrank_span_eq_card hbli
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan, hspan, finrank_top] at h1
    rw [← h1]
    simp
  have hex : ∀ x : b, ∃ α : Fin n → ℕ,
      (Finset.univ.filter (fun i => ℓ ≤ α i)).card ≤ d ∧
        x.1 = fun w => ∏ i, lam (w.1 i) ^ α i := fun x => hbs x.2
  choose α hα hαb using hex
  have hdir : ∀ i : Fin n, ∑ a ∈ finiteBehaviors W i, ((finiteFiber W i a).card - ℓ) ≤
      (Finset.univ.filter (fun x : b => ℓ ≤ α x i)).card := by
    intro i
    have h1 := per_dir ℓ W lam i (fun x : b => x.1) hbli α
      (fun x w => by rw [hαb x])
    have h2 : W.card = ∑ a ∈ finiteBehaviors W i, (finiteFiber W i a).card := by
      unfold finiteBehaviors finiteFiber
      exact Finset.card_eq_sum_card_image (away i) W
    have h3 : (Finset.univ.filter (fun x : b => α x i < ℓ)).card +
        (Finset.univ.filter (fun x : b => ℓ ≤ α x i)).card = W.card := by
      have e : (Finset.univ.filter (fun x : b => α x i < ℓ)) =
          (Finset.univ.filter (fun x : b => ¬ ℓ ≤ α x i)) := by
        ext x; simp
      rw [e, add_comm, Finset.card_filter_add_card_filter_not]; simp [hcardb]
    have h4 : ∑ a ∈ finiteBehaviors W i, ((finiteFiber W i a).card - ℓ) +
        ∑ a ∈ finiteBehaviors W i, min (finiteFiber W i a).card ℓ = W.card := by
      rw [h2, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _; omega
    omega
  calc ∑ i : Fin n, ∑ a ∈ finiteBehaviors W i, ((finiteFiber W i a).card - ℓ)
      ≤ ∑ i : Fin n, (Finset.univ.filter (fun x : b => ℓ ≤ α x i)).card :=
        Finset.sum_le_sum (fun i _ => hdir i)
    _ = ∑ x : b, (Finset.univ.filter (fun i : Fin n => ℓ ≤ α x i)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ x : b, d := Finset.sum_le_sum (fun x _ => hα x)
    _ = d * W.card := by
        rw [Finset.sum_const, Finset.card_univ, hcardb, smul_eq_mul, mul_comm]


theorem dim_relabel {X Y Z : Type*} {n : ℕ} (ℓ : ℕ) (H : Set (X → Y)) (S : Fin n → X)
    (W : Finset (Fin n → Y)) (hW : (↑W : Set (Fin n → Y)) ⊆ MulticlassDS.Compress.proj H S)
    (φ : Y → Z) (L : Set Y) (hL : ∀ w ∈ W, ∀ i, w i ∈ L) (hφ : Set.InjOn φ L) :
    listDSDim ℓ ((fun w : Fin n → Y => φ ∘ w) '' (↑W : Set (Fin n → Y))) ≤
      listDSDim ℓ H := by
  classical
  unfold listDSDim
  refine iSup_le fun m => iSup_le fun S' => iSup_le fun hsh => ?_
  obtain ⟨F, hFsub, hne, hnb⟩ := hsh
  have hex : ∀ v ∈ F, ∃ u : Fin m → Y, (∃ w ∈ W, u = w ∘ S') ∧ φ ∘ u = v := by
    intro v hv
    obtain ⟨u, ⟨w, hw, rfl⟩, rfl⟩ := hFsub hv
    exact ⟨w ∘ S', ⟨w, hw, rfl⟩, rfl⟩
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨u0, _⟩ := hex v0 hv0
  have : Nonempty (Fin m → Y) := ⟨u0⟩
  choose! ψ hψ using hex
  have hψL : ∀ v ∈ F, ∀ j, ψ v j ∈ L := by
    intro v hv j
    obtain ⟨⟨w, hw, he⟩, _⟩ := hψ v hv
    rw [he]; exact hL w hw _
  have hφψ : ∀ v ∈ F, ∀ j, φ (ψ v j) = v j := fun v hv j =>
    congrFun (hψ v hv).2 j
  have hinj : Set.InjOn ψ (↑F : Set (Fin m → Z)) := by
    intro v hv u hu h
    funext j
    rw [← hφψ v hv j, ← hφψ u hu j, h]
  have hshH : ListDSShatters ℓ H (S ∘ S') := by
    refine ⟨F.image ψ, ?_, ?_, ?_⟩
    · intro u hu
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      obtain ⟨⟨w, hw, he⟩, _⟩ := hψ v hv
      obtain ⟨h, hh, rfl⟩ := hW hw
      exact ⟨h, hh, by rw [he]; rfl⟩
    · exact ⟨ψ v0, Finset.mem_image_of_mem _ hv0⟩
    · intro u hu i
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
      refine le_trans (hnb v hv i) ?_
      refine Finset.card_le_card_of_injOn ψ ?_ (fun x hx y hy h => hinj (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1 h)
      intro g hg
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hg
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe]
      refine ⟨Finset.mem_image_of_mem _ hg.1, ?_, ?_⟩
      · intro h
        apply hg.2.1
        rw [← hφψ v hv i, ← hφψ g hg.1 i, h]
      · intro j hj
        have := hg.2.2 j hj
        apply hφ (hψL v hv j) (hψL g hg.1 j)
        rw [hφψ v hv j, hφψ g hg.1 j]; exact this
  exact le_iSup_of_le (S ∘ S') (le_iSup_of_le hshH le_rfl) |> fun h => le_trans (le_refl _) (le_iSup_of_le m h)


open scoped NNReal in
theorem density_bound {X Y : Type*} (H : Set (X → Y)) (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (s : ℕ)
    (hs : listDSDim ℓ H ≤ (s : ℕ∞)) (S : Fin n → X) (W : Finset (Fin n → Y))
    (hne : W.Nonempty) (hW : (↑W : Set (Fin n → Y)) ⊆ MulticlassDS.Compress.proj H S) :
    listDensity ℓ W ≤ (s : ℝ≥0) := by
  classical
  let L : Finset Y := W.biUnion (fun w => Finset.univ.image w)
  let φ : Y → Fin (L.card + 1) := fun y =>
    if h : y ∈ L then (L.equivFin ⟨y, h⟩).castSucc else Fin.last _
  have hLm : ∀ w ∈ W, ∀ i, w i ∈ (↑L : Set Y) := by
    intro w hw i
    simp only [Finset.mem_coe, L, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨w, hw, i, rfl⟩
  have hφ : Set.InjOn φ (↑L : Set Y) := by
    intro x hx y hy h
    simp only [Finset.mem_coe] at hx hy
    simp only [φ, hx, hy, dite_true] at h
    have := (L.equivFin).injective (Fin.castSucc_injective _ h)
    exact congrArg Subtype.val this
  let W' : Set (Fin n → Fin (L.card + 1)) := (fun w : Fin n → Y => φ ∘ w) '' (↑W : Set _)
  have hdim : listDSDim ℓ W' ≤ (s : ℕ∞) :=
    le_trans (dim_relabel ℓ H S W hW φ (↑L) hLm hφ) hs
  have hsp := spanning_lemma (L.card + 1) n ℓ s W' hℓ hdim
  let lam : Y → ℝ := fun y => realLabel (φ y)
  have hinjW : Function.Injective (fun w : ↥W => (⟨φ ∘ w.1, w.1, w.2, rfl⟩ : ↥W')) := by
    intro a b h
    have h' : φ ∘ a.1 = φ ∘ b.1 := congrArg Subtype.val h
    apply Subtype.ext
    funext i
    exact hφ (hLm a.1 a.2 i) (hLm b.1 b.2 i) (congrFun h' i)
  have hsurjW : Function.Surjective (fun w : ↥W => (⟨φ ∘ w.1, w.1, w.2, rfl⟩ : ↥W')) := by
    rintro ⟨_, w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  let e : ↥W ≃ ↥W' := Equiv.ofBijective _ ⟨hinjW, hsurjW⟩
  let T : (↥W' → ℝ) ≃ₗ[ℝ] (↥W → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e
  have hspan : Submodule.span ℝ {f : ↥W → ℝ | ∃ α : Fin n → ℕ,
      (Finset.univ.filter (fun i => ℓ ≤ α i)).card ≤ s ∧
        f = fun w => ∏ i, lam (w.1 i) ^ α i} = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have h1 : T.symm g ∈ Submodule.span ℝ (monomials ℓ s W') := by rw [hsp]; trivial
    have h2 : g ∈ Submodule.map (T : (↥W' → ℝ) →ₗ[ℝ] (↥W → ℝ))
        (Submodule.span ℝ (monomials ℓ s W')) :=
      ⟨T.symm g, h1, by simp⟩
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨f, ⟨α, _, hαs, rfl⟩, rfl⟩
    refine ⟨α, hαs, ?_⟩
    funext w
    rfl
  have hcore := core ℓ s W lam hspan
  have hpos : (0 : ℝ≥0) < (W.card : ℝ≥0) := by exact_mod_cast hne.card_pos
  unfold listDensity
  rw [div_le_iff₀ hpos]
  exact_mod_cast hcore

end DSDensity1246.Dev.Density

namespace DSDensity1246.Main
open scoped NNReal

/-- Theorem 1, pp. 3 and 14, (6): constant 1 and the ceiling are retained.
The extended-natural dimension also covers unbounded shattering. -/
theorem chk_density_le_ds {X Y : Type*} (H : Set (X → Y))
    (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 0 < n) :
    (⌈(maximumDensity ℓ H n : ℝ)⌉₊ : ℕ∞) ≤ listDSDim ℓ H := by
  classical
  rcases eq_or_ne (listDSDim ℓ H) ⊤ with h | h
  · rw [h]; exact le_top
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.1 h
  have hbd : maximumDensity ℓ H n ≤ (s : ℝ≥0) := by
    apply csSup_le'
    rintro r ⟨S, W, hne, hW, rfl⟩
    exact DSDensity1246.Dev.Density.density_bound H ℓ n hℓ s hs.ge S W hne hW
  rw [← hs]
  have : ⌈(maximumDensity ℓ H n : ℝ)⌉₊ ≤ s := by
    rw [Nat.ceil_le]
    exact_mod_cast hbd
  exact_mod_cast this

end DSDensity1246.Main
end

theorem solution : type_of% @DSDensity1246.Main.chk_density_le_ds := @DSDensity1246.Main.chk_density_le_ds
