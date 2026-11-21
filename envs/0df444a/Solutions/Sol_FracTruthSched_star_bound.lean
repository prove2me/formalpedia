-- Prove2me | solution 1 for FracTruthSched.star_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:22:15.199598+00:00
-- url     : https://prove2.me/submissions/3bfc510d-837d-4efe-9574-3b76d2db1059

import Mathlib
import Definitions.Def_FracTruthSched_CoreTask
import Definitions.Def_FracTruthSched_incident
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_disutility
import Definitions.Def_FracTruthSched_IsAdditiveOn
import Definitions.Def_FracTruthSched_IsSymmetricOn
import Definitions.Def_FracTruthSched_rootStarInput
import Definitions.Def_FracTruthSched_classSet
import Theorems.Thm_FracTruthSched_lemma_3
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_IsClassSymmetric
import Theorems.Thm_FracTruthSched_lemma_5

section
set_option autoImplicit false

namespace FracTruthSched.Dev.Star
open FracTruthSched

/-- the `k`-th edge between machines `i` and `j` (junk loop if `i = j`). Symmetric in `i j`. -/
def E {n ℓ : ℕ} (i j : Fin n) (k : Fin ℓ) : CoreTask n ℓ :=
  if h : i < j then Sum.inl (⟨(i, j), h⟩, k)
  else if h' : j < i then Sum.inl (⟨(j, i), h'⟩, k) else Sum.inr i

lemma E_symm {n ℓ : ℕ} (i j : Fin n) (k : Fin ℓ) : E i j k = E j i k := by
  rcases lt_trichotomy i j with h | h | h
  · simp [E, h, not_lt.mpr h.le]
  · subst h; simp [E]
  · simp [E, h, not_lt.mpr h.le]

lemma isLeft_E {n ℓ : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin ℓ) : (E i j k).isLeft := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [E, h]
  · simp [E, h, not_lt.mpr h.le]

lemma incident_E {n ℓ : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin ℓ) (u : Fin n) :
    incident u (E i j k) ↔ u = i ∨ u = j := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [E, h, incident]
  · simp [E, h, not_lt.mpr h.le, incident, or_comm]

lemma E_inj {n ℓ : ℕ} {i j : Fin n} (hij : i ≠ j) {k k' : Fin ℓ} (h : E i j k = E i j k') :
    k = k' := by
  rcases lt_or_gt_of_ne hij with h1 | h1
  · simp [E, h1] at h
    exact h
  · simp [E, h1, not_lt.mpr h1.le] at h
    exact h

/-- every left core task incident to `i` is some `E i j k` with `j ≠ i`. -/
lemma exists_E {n ℓ : ℕ} (i : Fin n) (e : CoreTask n ℓ) (hl : e.isLeft) (hi : incident i e) :
    ∃ j : Fin n, ∃ h : j ≠ i, ∃ k : Fin ℓ, E i j k = e := by
  rcases e with ⟨⟨⟨⟨a, b⟩, hab⟩, k⟩⟩ | _
  · simp only [incident] at hi
    rcases hi with rfl | rfl
    · exact ⟨b, (ne_of_gt hab), k, by simp [E, hab]⟩
    · exact ⟨a, (ne_of_lt hab), k, by simp [E, hab, not_lt.mpr hab.le]⟩
  · simp at hl

lemma E_ne_E {n ℓ : ℕ} {i j j' : Fin n} (hj : i ≠ j) (hj' : i ≠ j') (k k' : Fin ℓ)
    (h : E i j k = E i j' k') : j = j' ∧ k = k' := by
  have h1 := incident_E hj k j
  have h2 := incident_E hj' k' j
  rw [h] at h1
  have : j = j' := by
    rcases (h2.mp (h1.mpr (Or.inr rfl))) with h3 | h3
    · exact absurd h3.symm hj
    · exact h3
  subst this
  exact ⟨rfl, E_inj hj h⟩

end FracTruthSched.Dev.Star
end

section
set_option autoImplicit false

namespace FracTruthSched.Dev.StarA
open FracTruthSched FracTruthSched.Dev.Star


/-- the root-incident edges as an embedding of the star's coordinates -/
def phi {n' ℓ : ℕ} (i : Fin (n' + 1)) (d : Fin n' × Fin ℓ) : CoreTask (n' + 1) ℓ :=
  E i (i.succAbove d.1) d.2

lemma phi_inj {n' ℓ : ℕ} (i : Fin (n' + 1)) : Function.Injective (phi (ℓ := ℓ) i) := by
  intro d d' h
  have := E_ne_E (Fin.succAbove_ne i d.1).symm (Fin.succAbove_ne i d'.1).symm _ _ h
  exact Prod.ext (Fin.succAbove_right_injective this.1) this.2

lemma phi_left_inc {n' ℓ : ℕ} (i : Fin (n' + 1)) (d : Fin n' × Fin ℓ) :
    (phi i d).isLeft ∧ incident i (phi i d) :=
  ⟨isLeft_E (Fin.succAbove_ne i d.1).symm _,
    (incident_E (Fin.succAbove_ne i d.1).symm _ i).mpr (Or.inl rfl)⟩

lemma exists_phi {n' ℓ : ℕ} (i : Fin (n' + 1)) (e : CoreTask (n' + 1) ℓ) (hl : e.isLeft)
    (hi : incident i e) : ∃ d, phi i d = e := by
  obtain ⟨j, hj, k, hk⟩ := exists_E i e hl hi
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hj
  exact ⟨(a, k), hk⟩

/-- extension by zero -/
noncomputable def ext {n' ℓ : ℕ} (i : Fin (n' + 1)) (b : Fin n' × Fin ℓ → ℝ) :
    CoreTask (n' + 1) ℓ → ℝ := Function.extend (phi i) b 0

lemma ext_phi {n' ℓ : ℕ} (i : Fin (n' + 1)) (b : Fin n' × Fin ℓ → ℝ) (d : Fin n' × Fin ℓ) :
    ext i b (phi i d) = b d := (phi_inj i).extend_apply b 0 d

lemma ext_nonneg {n' ℓ : ℕ} (i : Fin (n' + 1)) (b : Fin n' × Fin ℓ → ℝ) (hb : ∀ d, 0 ≤ b d)
    (e : CoreTask (n' + 1) ℓ) : 0 ≤ ext i b e := by
  by_cases h : ∃ d, phi i d = e
  · obtain ⟨d, rfl⟩ := h
    rw [ext_phi]; exact hb d
  · simp only [ext]
    rw [Function.extend_apply' _ _ _ h]
    simp

lemma rsi_congr {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (c c' : CoreTask (n' + 1) ℓ → ℝ)
    (hc : ∀ e, e.isLeft → incident i e → c e = c' e) :
    rootStarInput i lam c = rootStarInput i lam c' := by
  funext u e
  by_cases h : e.isLeft ∧ incident i e ∧ incident u e
  · simp [rootStarInput, h, hc e h.1 h.2.1]
  · simp [rootStarInput, h]

lemma rsi_of_ne {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (c c' : CoreTask (n' + 1) ℓ → ℝ)
    (u : Fin (n' + 1)) (hu : u ≠ i) :
    rootStarInput i lam c u = rootStarInput i lam c' u := by
  funext e
  simp [rootStarInput, hu]

lemma rsi_self_zero {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (c : CoreTask (n' + 1) ℓ → ℝ)
    (e : CoreTask (n' + 1) ℓ) (h : ¬ (e.isLeft ∧ incident i e)) :
    rootStarInput i lam c i e = 0 := by
  simp [rootStarInput]
  intro h1 h2
  exact absurd ⟨h1, h2⟩ h

/-- the star input -/
noncomputable def Tin {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (b : Fin n' × Fin ℓ → ℝ) :
    Fin (n' + 1) → CoreTask (n' + 1) ℓ → ℝ := rootStarInput i lam (ext i b)

lemma Tin_self_phi {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (b : Fin n' × Fin ℓ → ℝ)
    (d : Fin n' × Fin ℓ) : Tin i lam b i (phi i d) = b d := by
  have h := phi_left_inc i d
  simp [Tin, rootStarInput, h.1, h.2, ext_phi]

lemma graph_Tin {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (hlam : 0 ≤ lam)
    (b : Fin n' × Fin ℓ → ℝ) (hb : ∀ d, 0 ≤ b d) : IsGraphInput (Tin i lam b) := by
  intro u e
  constructor
  · unfold Tin rootStarInput
    split_ifs
    · exact ext_nonneg i b hb e
    · exact hlam
    · exact le_rfl
  · intro hn
    unfold Tin rootStarInput
    rw [if_neg]
    intro h
    exact hn h.2.2

lemma update_Tin {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (b b' : Fin n' × Fin ℓ → ℝ) :
    Function.update (Tin i lam b) i (Tin i lam b' i) = Tin i lam b' := by
  funext u
  by_cases hu : u = i
  · subst hu; simp
  · rw [Function.update_of_ne hu]
    exact rsi_of_ne i lam _ _ u hu

lemma update0_Tin {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (b b' : Fin n' × Fin ℓ → ℝ) :
    Function.update (Tin i lam b) i 0 = Function.update (Tin i lam b') i 0 := by
  funext u
  by_cases hu : u = i
  · subst hu; simp
  · rw [Function.update_of_ne hu, Function.update_of_ne hu]
    exact rsi_of_ne i lam _ _ u hu

lemma sum_reduce {n' ℓ : ℕ} (i : Fin (n' + 1)) (g : CoreTask (n' + 1) ℓ → ℝ)
    (h : ∀ e, ¬ (e.isLeft ∧ incident i e) → g e = 0) :
    ∑ e, g e = ∑ d, g (phi i d) := by
  rw [← Finset.sum_image (f := g) (s := Finset.univ) (g := phi i)
    (fun x _ y _ hxy => phi_inj i hxy)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  apply h
  rintro ⟨h1, h2⟩
  obtain ⟨d, hd⟩ := exists_phi i e h1 h2
  exact he (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd⟩)

lemma rowsum {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ)) (i : Fin (n' + 1))
    (lam : ℝ) (b b' : Fin n' × Fin ℓ → ℝ) :
    ∑ e, Tin i lam b i e * M.x (Tin i lam b') i e =
      ∑ d, b d * M.x (Tin i lam b') i (phi i d) := by
  rw [sum_reduce i (fun e => Tin i lam b i e * M.x (Tin i lam b') i e)]
  · simp only [Tin_self_phi]
  · intro e he
    simp [Tin, rsi_self_zero i lam _ e he]

lemma inc_ineq {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ))
    (htruth : IsTruthfulOn IsGraphInput M) (i : Fin (n' + 1)) (lam : ℝ) (hlam : 0 ≤ lam)
    (b b' : Fin n' × Fin ℓ → ℝ) (hb : ∀ d, 0 ≤ b d) (hb' : ∀ d, 0 ≤ b' d) :
    ∑ d, M.x (Tin i lam b') i (phi i d) * (b' d - b d) ≤
        disutility M (Tin i lam b') i - disutility M (Tin i lam b) i ∧
      disutility M (Tin i lam b') i - disutility M (Tin i lam b) i ≤
        ∑ d, M.x (Tin i lam b) i (phi i d) * (b' d - b d) := by
  have h1 := htruth (Tin i lam b) (graph_Tin i lam hlam b hb) i (Tin i lam b' i)
    (by rw [update_Tin]; exact graph_Tin i lam hlam b' hb')
  rw [update_Tin] at h1
  have h2 := htruth (Tin i lam b') (graph_Tin i lam hlam b' hb') i (Tin i lam b i)
    (by rw [update_Tin]; exact graph_Tin i lam hlam b hb)
  rw [update_Tin] at h2
  have r1 := rowsum M i lam b b'
  have r2 := rowsum M i lam b b
  have r3 := rowsum M i lam b' b'
  have r4 := rowsum M i lam b' b
  have h0 := update0_Tin i lam b b'
  have s1 : ∑ d, M.x (Tin i lam b') i (phi i d) * (b' d - b d) =
      ∑ d, b' d * M.x (Tin i lam b') i (phi i d) - ∑ d, b d * M.x (Tin i lam b') i (phi i d) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  have s2 : ∑ d, M.x (Tin i lam b) i (phi i d) * (b' d - b d) =
      ∑ d, b' d * M.x (Tin i lam b) i (phi i d) - ∑ d, b d * M.x (Tin i lam b) i (phi i d) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  simp only [disutility]
  rw [h0]
  constructor <;> linarith

lemma W_congr {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ)) (i : Fin (n' + 1))
    (lam : ℝ) (c : CoreTask (n' + 1) ℓ → ℝ) (b : Fin n' × Fin ℓ → ℝ)
    (hc : ∀ d, c (phi i d) = b d) :
    disutility M (rootStarInput i lam c) i = disutility M (Tin i lam b) i := by
  have : rootStarInput i lam c = Tin i lam b := by
    apply rsi_congr
    intro e hl hi
    obtain ⟨d, rfl⟩ := exists_phi i e hl hi
    rw [hc, ext_phi]
  rw [this]

lemma add_transfer {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ)) (i : Fin (n' + 1))
    (lam : ℝ) (F : Finset (Fin n' × Fin ℓ))
    (h : IsAdditiveOn (fun a => disutility M (rootStarInput i lam a) i) (F.image (phi i))) :
    IsAdditiveOn (fun b => disutility M (Tin i lam b) i) F := by
  intro b hb
  have key := h (ext i b) (ext_nonneg i b hb)
  beta_reduce at key ⊢
  have e1 : disutility M (rootStarInput i lam (ext i b)) i = disutility M (Tin i lam b) i := rfl
  have e2 : disutility M (rootStarInput i lam
      (fun e => if e ∈ F.image (phi i) then 0 else ext i b e)) i =
      disutility M (Tin i lam (fun d => if d ∈ F then 0 else b d)) i := by
    apply W_congr
    intro d
    simp [(phi_inj i).mem_finset_image, ext_phi]
  rw [e1, e2, Finset.sum_image (fun x _ y _ hxy => phi_inj i hxy)] at key
  rw [key]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply W_congr
  intro d'
  by_cases hdd : d' = d
  · subst hdd
    simp [ext_phi]
  · have : phi i d' ≠ phi i d := fun hh => hdd (phi_inj i hh)
    simp only [Function.update_of_ne this, Function.update_of_ne hdd,
      (phi_inj i).mem_finset_image, ext_phi]

lemma sym_transfer {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ)) (i : Fin (n' + 1))
    (lam : ℝ) (F : Finset (Fin n' × Fin ℓ))
    (h : IsSymmetricOn (fun a => disutility M (rootStarInput i lam a) i) (F.image (phi i))) :
    IsSymmetricOn (fun b => disutility M (Tin i lam b) i) F := by
  classical
  intro σ hσ b hb
  let σ' : Equiv.Perm (CoreTask (n' + 1) ℓ) :=
    σ.extendDomain (Equiv.ofInjective (phi (ℓ := ℓ) i) (phi_inj i))
  have hσ' : ∀ d, σ' (phi i d) = phi i (σ d) := by
    intro d
    have := Equiv.Perm.extendDomain_apply_image σ (Equiv.ofInjective (phi (ℓ := ℓ) i) (phi_inj i)) d
    simpa [σ'] using this
  have hfix : ∀ e, e ∉ F.image (phi i) → σ' e = e := by
    intro e he
    by_cases hr : ∃ d, phi i d = e
    · obtain ⟨d, rfl⟩ := hr
      have hd : d ∉ F := fun hh => he (Finset.mem_image.mpr ⟨d, hh, rfl⟩)
      rw [hσ', hσ d hd]
    · exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simpa using hr)
  have key := h σ' hfix (ext i b) (ext_nonneg i b hb)
  beta_reduce at key ⊢
  have e1 : disutility M (rootStarInput i lam (ext i b)) i = disutility M (Tin i lam b) i := rfl
  have e2 : disutility M (rootStarInput i lam (ext i b ∘ σ')) i =
      disutility M (Tin i lam (b ∘ σ)) i := by
    apply W_congr
    intro d
    simp [hσ', ext_phi]
  rw [e1, e2] at key
  exact key

lemma classSet_eq {n' ℓ : ℕ} (i : Fin (n' + 1)) (a : Fin n') :
    classSet (ℓ := ℓ) i (i.succAbove a) =
      (Finset.univ.filter (fun d : Fin n' × Fin ℓ => d.1 = a)).image (phi i) := by
  ext e
  simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hl, hi, hj⟩
    obtain ⟨j, hj', k, hk⟩ := exists_E i e hl hi
    subst hk
    rw [incident_E hj'.symm] at hj
    rcases hj with h | h
    · exact absurd h (Fin.succAbove_ne i a)
    · obtain ⟨a', rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hj'
      exact ⟨(a, k), rfl, by simp [phi, h]⟩
  · rintro ⟨d, hd, rfl⟩
    have h := phi_left_inc i d
    refine ⟨h.1, h.2, ?_⟩
    simp only [phi]
    rw [incident_E (Fin.succAbove_ne i d.1).symm]
    right; rw [hd]

/-- TARGET (to be proved, no sorry). Transfer of the published `lemma_3` to the root's disutility. -/
theorem pieceA {n' ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (i : Fin (n' + 1)) (lam : ℝ) (hlam : 0 ≤ lam)
    (hadd : ∀ j, j ≠ i → IsAdditiveOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j))
    (hsym : ∀ j, j ≠ i → IsSymmetricOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j))
    (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - 1 / (ℓ : ℝ)) ^ (n' - 1) *
        ∑ a : Fin n', M.x (rootStarInput i lam (Pi.single (E i (i.succAbove a) (⟨0, by omega⟩ : Fin ℓ)) 1)) i
          (E i (i.succAbove a) ⟨0, by omega⟩) ≤
      ∑ a : Fin n', M.x (rootStarInput i lam
          (fun d => if d ∈ Finset.univ.image (fun a : Fin n' => E i (i.succAbove a) (⟨0, by omega⟩ : Fin ℓ))
            then u else 0)) i (E i (i.succAbove a) ⟨0, by omega⟩) := by
  classical
  have hcard : ∀ j : Fin n', (Finset.univ.filter (fun d : Fin n' × Fin ℓ => d.1 = j)).card = ℓ := by
    intro j
    have : (Finset.univ.filter (fun d : Fin n' × Fin ℓ => d.1 = j)) =
        ({j} : Finset (Fin n')) ×ˢ (Finset.univ : Finset (Fin ℓ)) := by
      ext d; simp [Prod.ext_iff, eq_comm]
    rw [this]; simp
  have hℓ0 : 0 < ℓ := by omega
  have main := lemma_3 (τ := Fin n' × Fin ℓ) (k := n') (ℓ := ℓ) Prod.fst hcard
    (fun b => disutility M (Tin i lam b) i) (fun b d => M.x (Tin i lam b) i (phi i d))
    (by
      intro b hb d
      exact (hfeas _ (graph_Tin i lam hlam b hb)).1 i _ |>.1)
    (fun b b' hb hb' => inc_ineq M htruth i lam hlam b b' hb hb')
    (fun a => by
      have := hadd (i.succAbove a) (Fin.succAbove_ne i a)
      rw [classSet_eq] at this
      exact add_transfer M i lam _ this)
    (fun a => by
      have := hsym (i.succAbove a) (Fin.succAbove_ne i a)
      rw [classSet_eq] at this
      exact sym_transfer M i lam _ this)
    (fun a => (a, ⟨0, hℓ0⟩)) (fun a => rfl) u hu
  have h1 : ∀ a : Fin n', rootStarInput i lam
      (Pi.single (E i (i.succAbove a) (⟨0, hℓ0⟩ : Fin ℓ)) (1 : ℝ)) =
      Tin i lam (Pi.single (a, ⟨0, hℓ0⟩) 1) := by
    intro a
    apply rsi_congr
    intro e hl hi
    obtain ⟨d, rfl⟩ := exists_phi i e hl hi
    have : E i (i.succAbove a) (⟨0, hℓ0⟩ : Fin ℓ) = phi i (a, ⟨0, hℓ0⟩) := rfl
    rw [this, ext_phi]
    simp only [Pi.single_apply, (phi_inj i).eq_iff]
  have h2 : rootStarInput i lam
      (fun d => if d ∈ Finset.univ.image (fun a : Fin n' => E i (i.succAbove a) (⟨0, hℓ0⟩ : Fin ℓ))
        then u else 0) =
      Tin i lam (fun d => if d ∈ Finset.univ.image (fun a : Fin n' => (a, (⟨0, hℓ0⟩ : Fin ℓ)))
        then u else 0) := by
    apply rsi_congr
    intro e hl hi
    obtain ⟨d, rfl⟩ := exists_phi i e hl hi
    rw [ext_phi]
    have : (phi i d ∈ Finset.univ.image (fun a : Fin n' => E i (i.succAbove a) (⟨0, hℓ0⟩ : Fin ℓ))) ↔
        d ∈ Finset.univ.image (fun a : Fin n' => (a, (⟨0, hℓ0⟩ : Fin ℓ))) := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha⟩
        have := E_ne_E (Fin.succAbove_ne i a).symm (Fin.succAbove_ne i d.1).symm _ _ ha
        exact ⟨a, Prod.ext (Fin.succAbove_right_injective this.1) this.2⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
    simp only [this]
  simp only [h1, h2]
  exact main

end FracTruthSched.Dev.StarA
end

section
set_option autoImplicit false
namespace FracTruthSched.Dev.StarB1
open FracTruthSched FracTruthSched.Dev.Star

def I {n ℓ : ℕ} (i j : Fin n) (k : Fin ℓ) : Fin n → CoreTask n ℓ → ℝ :=
  fun u e => if e = E i j k ∧ incident u e then 1 else 0

def Jn {n ℓ : ℕ} (i : Fin n) (lam : ℝ) (e : CoreTask n ℓ) (S : Finset (CoreTask n ℓ)) :
    Fin n → CoreTask n ℓ → ℝ :=
  fun u f => if f = e ∨ f ∈ S then rootStarInput i lam (Pi.single e 1) u f else 0

lemma isGraph_I {n ℓ : ℕ} (i j : Fin n) (k : Fin ℓ) : IsGraphInput (I i j k) := by
  intro u e
  unfold I
  split_ifs with h
  · exact ⟨zero_le_one, fun hn => absurd h.2 hn⟩
  · exact ⟨le_refl _, fun _ => rfl⟩

lemma isGraph_T {n ℓ : ℕ} (i : Fin n) {lam : ℝ} (hlam : 0 ≤ lam) (e : CoreTask n ℓ) :
    IsGraphInput (rootStarInput i lam (Pi.single e 1)) := by
  intro u f
  unfold rootStarInput
  split_ifs with h h2
  · refine ⟨?_, fun hn => absurd h.2.2 hn⟩
    rw [Pi.single_apply]; split_ifs <;> norm_num
  · exact ⟨hlam, fun hn => absurd h.2.2 hn⟩
  · exact ⟨le_refl _, fun _ => rfl⟩

lemma isGraph_Jn {n ℓ : ℕ} (i : Fin n) {lam : ℝ} (hlam : 0 ≤ lam) (e : CoreTask n ℓ)
    (S : Finset (CoreTask n ℓ)) : IsGraphInput (Jn i lam e S) := by
  intro u f
  have := isGraph_T i hlam e u f
  unfold Jn
  split_ifs
  · exact this
  · exact ⟨le_refl _, fun _ => rfl⟩

lemma pair_sum {n ℓ : ℕ} {M : FracMech n (CoreTask n ℓ)} (hfeas : IsFeasibleOn IsGraphInput M)
    (hel : IsEligible M) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) {i j : Fin n}
    (hij : i ≠ j) (k : Fin ℓ) : M.x t i (E i j k) + M.x t j (E i j k) = 1 := by
  have h1 := (hfeas t ht).2 (E i j k)
  rw [Fintype.sum_eq_add i j hij] at h1
  · exact h1
  · intro c hc
    apply hel t ht
    rw [incident_E hij]
    tauto

lemma I_symm {n ℓ : ℕ} (i j : Fin n) (k : Fin ℓ) : I j i k = I i j k := by
  funext u e
  simp only [I, E_symm j i k]

lemma w_sum {n ℓ : ℕ} {M : FracMech n (CoreTask n ℓ)} (hfeas : IsFeasibleOn IsGraphInput M)
    (hel : IsEligible M) {i j : Fin n} (hij : i ≠ j) (k : Fin ℓ) :
    M.x (I i j k) i (E i j k) + M.x (I j i k) j (E j i k) = 1 := by
  rw [I_symm i j k, E_symm j i k]
  exact pair_sum hfeas hel (isGraph_I i j k) hij k

lemma wmon {n ℓ : ℕ} {M : FracMech n (CoreTask n ℓ)} (htruth : IsTruthfulOn IsGraphInput M)
    {t t' : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (ht' : IsGraphInput t') (j : Fin n)
    (hrow : ∀ u, u ≠ j → t u = t' u) :
    ∑ f, (t' j f - t j f) * (M.x t' j f - M.x t j f) ≤ 0 := by
  have e1 : Function.update t j (t' j) = t' := by
    funext u
    by_cases h : u = j
    · subst h; simp
    · simp [h, hrow u h]
  have e2 : Function.update t' j (t j) = t := by
    funext u
    by_cases h : u = j
    · subst h; simp
    · simp [h, hrow u h]
  have h1 := htruth t ht j (t' j) (by rw [e1]; exact ht')
  rw [e1] at h1
  have h2 := htruth t' ht' j (t j) (by rw [e2]; exact ht)
  rw [e2] at h2
  have : ∑ f, (t' j f - t j f) * (M.x t' j f - M.x t j f) =
      ∑ f, t' j f * M.x t' j f - ∑ f, t' j f * M.x t j f - ∑ f, t j f * M.x t' j f
        + ∑ f, t j f * M.x t j f := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros; ring
  rw [this]
  linarith

lemma T_i_ne {n ℓ : ℕ} (i : Fin n) (lam : ℝ) {e f : CoreTask n ℓ} (hf : f ≠ e) :
    rootStarInput i lam (Pi.single e 1) i f = 0 := by
  simp [rootStarInput, Pi.single_apply, hf]

lemma Jn_const {n ℓ : ℕ} {M : FracMech n (CoreTask n ℓ)} (hzti : HasZeroTypeIrrelevance M)
    (i : Fin n) {lam : ℝ} (hlam : 0 ≤ lam) (e : CoreTask n ℓ) (S : Finset (CoreTask n ℓ)) :
    M.x (Jn i lam e S) i e = M.x (Jn i lam e ∅) i e := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert f S hfS ih =>
    rw [← ih]
    by_cases hc : f ≠ e ∧ f.isLeft ∧ incident i f
    · obtain ⟨hfe, hl, hinc⟩ := hc
      have := hzti (Jn i lam e S) (Jn i lam e (insert f S)) (isGraph_Jn i hlam e S)
        (isGraph_Jn i hlam e _) f hl
        (by
          intro u g hg
          simp [Jn, hg])
        ⟨i, hinc, by simp [Jn, T_i_ne i lam hfe]⟩
        ⟨i, hinc, by simp [Jn, T_i_ne i lam hfe]⟩ i e (Ne.symm hfe)
      exact this.symm
    · have : Jn i lam e (insert f S) = Jn i lam e S := by
        funext u g
        by_cases hg : g = f
        · subst hg
          by_cases hge : g = e
          · simp [Jn, hge]
          · have h0 : rootStarInput i lam (Pi.single e 1) u g = 0 := by
              unfold rootStarInput
              rw [if_neg]
              intro h
              exact hc ⟨hge, h.1, h.2.1⟩
            simp [Jn, h0]
        · simp [Jn, hg]
      rw [this]

lemma key {n ℓ : ℕ} {M : FracMech n (CoreTask n ℓ)} (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M)
    {i j : Fin n} (hij : i ≠ j) (k : Fin ℓ) {lam : ℝ} (hlam : 1 ≤ lam) :
    M.x (I i j k) i (E i j k) ≤
      M.x (rootStarInput i lam (Pi.single (E i j k) 1)) i (E i j k) := by
  classical
  have hlam0 : 0 ≤ lam := by linarith
  set e := E i j k with he
  have hl : e.isLeft := isLeft_E hij k
  have hinc : ∀ u, incident u e ↔ u = i ∨ u = j := fun u => incident_E hij k u
  have Tie : rootStarInput i lam (Pi.single e 1) i e = 1 := by
    simp [rootStarInput, hl, hinc]
  have Tje : rootStarInput i lam (Pi.single e 1) j e = lam := by
    simp [rootStarInput, hl, hinc, hij.symm]
  have Tue : ∀ u, u ≠ i → u ≠ j → rootStarInput i lam (Pi.single e 1) u e = 0 := by
    intro u h1 h2
    have := (isGraph_T i hlam0 e u e).2
    apply this
    rw [hinc]; tauto
  have hIe : ∀ u, I i j k u e = if u = i ∨ u = j then 1 else 0 := by
    intro u
    simp [I, ← he, hinc]
  have hJe : ∀ u, Jn i lam e ∅ u e = rootStarInput i lam (Pi.single e 1) u e := by
    intro u
    simp [Jn]
  have hrow : ∀ u, (u ≠ j ∨ lam = 1) → I i j k u = Jn i lam e ∅ u := by
    intro u hu
    funext f
    by_cases hf : f = e
    · rw [hf, hIe, hJe]
      by_cases h1 : u = i
      · rw [h1, Tie]; simp
      · by_cases h2 : u = j
        · rw [h2, Tje]
          rcases hu with hu | hu
          · exact absurd h2 hu
          · simp [hu]
        · rw [Tue u h1 h2]; simp [h1, h2]
    · simp [I, Jn, hf, ← he]
  have hI0 := isGraph_I i j k
  have hJ0 := isGraph_Jn i hlam0 e ∅
  have hmono : M.x (Jn i lam e ∅) j e ≤ M.x (I i j k) j e := by
    rcases hlam.eq_or_lt with h | h
    · have : Jn i lam e ∅ = I i j k := by
        funext u
        exact (hrow u (Or.inr h.symm)).symm
      rw [this]
    · have hw := wmon htruth hI0 hJ0 j (fun u hu => hrow u (Or.inl hu))
      rw [Finset.sum_eq_single e] at hw
      · have a1 : Jn i lam e ∅ j e = lam := by simp [Jn, Tje]
        have a2 : I i j k j e = 1 := by rw [hIe]; simp
        rw [a1, a2] at hw
        by_contra hc
        push Not at hc
        nlinarith
      · intro f _ hf
        simp [Jn, I, hf, ← he]
      · simp
  have p0 := pair_sum hfeas hel hI0 hij k
  have p1 := pair_sum hfeas hel hJ0 hij k
  have hfin : M.x (rootStarInput i lam (Pi.single e 1)) i e = M.x (Jn i lam e ∅) i e := by
    have hT : rootStarInput i lam (Pi.single e 1) = Jn i lam e Finset.univ := by
      funext u f
      simp [Jn]
    rw [hT, Jn_const hzti i hlam0 e]
  rw [hfin]
  linarith

theorem pieceB1 {n' ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M) :
    ∃ i : Fin (n' + 1), ∀ lam : ℝ, 1 ≤ lam →
      (n' : ℝ) / 2 ≤ ∑ a : Fin n',
        M.x (rootStarInput i lam (Pi.single (E i (i.succAbove a) (⟨0, by omega⟩ : Fin ℓ)) 1)) i
          (E i (i.succAbove a) ⟨0, by omega⟩) := by
  classical
  set k0 : Fin ℓ := ⟨0, by omega⟩ with hk0
  let w : Fin (n' + 1) → Fin (n' + 1) → ℝ := fun i j => M.x (I i j k0) i (E i j k0)
  let W : Fin (n' + 1) → Fin (n' + 1) → ℝ := fun i j => if i = j then 1 / 2 else w i j
  have hW : ∀ i j, W i j + W j i = 1 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [W]; norm_num
    · have := w_sum hfeas hel h k0
      simp only [W, if_neg h, if_neg (Ne.symm h)]
      exact this
  have h2S : 2 * ∑ i, ∑ j, W i j = ((n' : ℝ) + 1) ^ 2 := by
    have : ∑ i, ∑ j, W j i = ∑ i, ∑ j, W i j := Finset.sum_comm
    have h3 : ∑ i, ∑ j, (W i j + W j i) = ((n' : ℝ) + 1) ^ 2 := by
      simp only [hW]
      simp
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)] at h3
    rw [Finset.sum_add_distrib, this] at h3
    linarith
  let f : Fin (n' + 1) → ℝ := fun i => ∑ a : Fin n', w i (i.succAbove a)
  have hrow : ∀ i, ∑ j, W i j = 1 / 2 + f i := by
    intro i
    rw [Fin.sum_univ_succAbove _ i]
    congr 1
    · simp [W]
    · apply Finset.sum_congr rfl
      intro a _
      simp only [W, if_neg (Fin.succAbove_ne i a).symm]
  have hsumf : ∑ i, f i = ((n' : ℝ) + 1) * n' / 2 := by
    have : ∑ i, ∑ j, W i j = ∑ i, (1 / 2 + f i) := Finset.sum_congr rfl (fun i _ => hrow i)
    rw [Finset.sum_add_distrib] at this
    simp at this
    nlinarith
  have hex : ∃ i, (n' : ℝ) / 2 ≤ f i := by
    by_contra h
    push Not at h
    have := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun i _ => h i)
    simp at this
    nlinarith
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, fun lam hlam => le_trans hi ?_⟩
  apply Finset.sum_le_sum
  intro a _
  exact key hfeas htruth hel hzti (Fin.succAbove_ne i a).symm k0 hlam

end FracTruthSched.Dev.StarB1
end

section
set_option autoImplicit false

namespace FracTruthSched
open FracTruthSched.Dev.Star

namespace Dev.StarB2

def ee {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (a : Fin n') : CoreTask (n' + 1) ℓ :=
  E i (i.succAbove a) k

def SS {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) : Finset (CoreTask (n' + 1) ℓ) :=
  Finset.univ.image (ee i k)

def Iu {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (lam u : ℝ) : Fin (n' + 1) → CoreTask (n' + 1) ℓ → ℝ :=
  rootStarInput i lam (fun d => if d ∈ SS i k then u else 0)

def rowc {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (c : ℝ) : CoreTask (n' + 1) ℓ → ℝ :=
  fun e => if e = Sum.inr i then 1 else if e ∈ SS i k then c else 0

def Is {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (lam u c : ℝ) :
    Fin (n' + 1) → CoreTask (n' + 1) ℓ → ℝ :=
  Function.update (Iu i k lam u) i (rowc i k c)

lemma ee_inj {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {a b : Fin n'}
    (h : ee i k a = ee i k b) : a = b := by
  have := E_ne_E (Fin.succAbove_ne i a).symm (Fin.succAbove_ne i b).symm k k h
  exact Fin.succAbove_right_injective this.1

lemma ee_isLeft {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (a : Fin n') : (ee i k a).isLeft :=
  isLeft_E (Fin.succAbove_ne i a).symm k

lemma ee_inc_root {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (a : Fin n') : incident i (ee i k a) :=
  (incident_E (Fin.succAbove_ne i a).symm k i).2 (Or.inl rfl)

lemma ee_inc_leaf {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (a : Fin n') :
    incident (i.succAbove a) (ee i k a) :=
  (incident_E (Fin.succAbove_ne i a).symm k _).2 (Or.inr rfl)

lemma mem_SS {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (e : CoreTask (n' + 1) ℓ) :
    e ∈ SS i k ↔ ∃ a, ee i k a = e := by
  simp [SS]

lemma mem_SS_prop {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {e : CoreTask (n' + 1) ℓ}
    (h : e ∈ SS i k) : e.isLeft ∧ incident i e := by
  obtain ⟨a, rfl⟩ := (mem_SS i k e).1 h
  exact ⟨ee_isLeft i k a, ee_inc_root i k a⟩

lemma loop_notMem {n' ℓ : ℕ} (i m : Fin (n' + 1)) (k : Fin ℓ) : (Sum.inr m : CoreTask (n' + 1) ℓ) ∉ SS i k := by
  intro h
  have := (mem_SS_prop i k h).1
  simp at this

lemma graph_root {n' ℓ : ℕ} (i : Fin (n' + 1)) (lam : ℝ) (a : CoreTask (n' + 1) ℓ → ℝ)
    (hl : 0 ≤ lam) (ha : ∀ e, 0 ≤ a e) : IsGraphInput (rootStarInput i lam a) := by
  intro m e
  unfold rootStarInput
  constructor
  · split_ifs <;> simp [ha e, hl]
  · intro hn
    rw [if_neg (fun h => hn h.2.2)]

lemma graph_Iu {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {lam u : ℝ} (hl : 0 ≤ lam) (hu : 0 ≤ u) :
    IsGraphInput (Iu i k lam u) :=
  graph_root i lam _ hl (fun e => by split_ifs <;> simp [hu])

lemma rowc_nonneg {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {c : ℝ} (hc : 0 ≤ c) (e : CoreTask (n' + 1) ℓ) :
    0 ≤ rowc i k c e := by
  unfold rowc; split_ifs <;> simp [hc]

lemma graph_Is {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {lam u c : ℝ} (hl : 0 ≤ lam) (hu : 0 ≤ u)
    (hc : 0 ≤ c) : IsGraphInput (Is i k lam u c) := by
  intro m e
  by_cases hm : m = i
  · subst hm
    simp only [Is, Function.update_self]
    refine ⟨rowc_nonneg m k hc e, fun hn => ?_⟩
    unfold rowc
    rw [if_neg, if_neg]
    · intro h; exact hn (incident_of_mem_SS' m k h)
    · rintro rfl; exact hn rfl
  · simp only [Is, Function.update_of_ne hm]
    exact graph_Iu i k hl hu m e
where incident_of_mem_SS' {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {e : CoreTask (n' + 1) ℓ}
    (h : e ∈ SS i k) : incident i e := (mem_SS_prop i k h).2

lemma Iu_root {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (lam u : ℝ) (e : CoreTask (n' + 1) ℓ) :
    Iu i k lam u i e = if e ∈ SS i k then u else 0 := by
  by_cases h : e ∈ SS i k
  · have := mem_SS_prop i k h
    simp [Iu, rootStarInput, h, this]
  · simp [Iu, rootStarInput, h]

lemma Iu_other {n' ℓ : ℕ} (i m : Fin (n' + 1)) (hm : m ≠ i) (k : Fin ℓ) (lam u : ℝ)
    (e : CoreTask (n' + 1) ℓ) :
    Iu i k lam u m e = if e.isLeft ∧ incident i e ∧ incident m e then lam else 0 := by
  simp [Iu, rootStarInput, hm]

lemma x_loop {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (hel : IsEligible M)
    (t : Fin (n' + 1) → CoreTask (n' + 1) ℓ → ℝ) (ht : IsGraphInput t) (i : Fin (n' + 1)) :
    M.x t i (Sum.inr i) = 1 := by
  have h := (hfeas t ht).2 (Sum.inr i)
  rw [Finset.sum_eq_single i] at h
  · exact h
  · intro b _ hb
    exact hel t ht b _ (fun h => hb h)
  · simp

lemma sumS {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (f : CoreTask (n' + 1) ℓ → ℝ) :
    ∑ e, (if e ∈ SS i k then f e else 0) = ∑ a, f (ee i k a) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_image (fun a _ b _ h => ee_inj i k h)

lemma sum_row {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (c : ℝ) (g : CoreTask (n' + 1) ℓ → ℝ) :
    ∑ e, rowc i k c e * g e = g (Sum.inr i) + c * ∑ a, g (ee i k a) := by
  have h1 : ∀ e, rowc i k c e * g e =
      (if e = Sum.inr i then g e else 0) + (if e ∈ SS i k then c * g e else 0) := by
    intro e
    unfold rowc
    by_cases h : e = Sum.inr i
    · subst h; simp [loop_notMem i i k]
    · by_cases h2 : e ∈ SS i k <;> simp [h, h2]
  rw [Finset.sum_congr rfl (fun e _ => h1 e), Finset.sum_add_distrib, Finset.sum_ite_eq',
    sumS i k (fun e => c * g e), ← Finset.mul_sum]
  simp

lemma sum_Iu {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (lam u : ℝ) (g : CoreTask (n' + 1) ℓ → ℝ) :
    ∑ e, Iu i k lam u i e * g e = u * ∑ a, g (ee i k a) := by
  have h1 : ∀ e, Iu i k lam u i e * g e = (if e ∈ SS i k then u * g e else 0) := by
    intro e; rw [Iu_root]; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun e _ => h1 e), sumS i k (fun e => u * g e), ← Finset.mul_sum]

lemma wmon {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ))
    (htruth : IsTruthfulOn IsGraphInput M) (t : Fin (n' + 1) → CoreTask (n' + 1) ℓ → ℝ)
    (i : Fin (n' + 1)) (b : CoreTask (n' + 1) ℓ → ℝ) (ht : IsGraphInput t)
    (hb : IsGraphInput (Function.update t i b)) :
    ∑ e, (b e - t i e) * (M.x (Function.update t i b) i e - M.x t i e) ≤ 0 := by
  have h1 := htruth t ht i b hb
  have h2 := htruth (Function.update t i b) hb i (t i)
    (by rwa [Function.update_idem, Function.update_eq_self])
  simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at h2
  have : ∑ e, (b e - t i e) * (M.x (Function.update t i b) i e - M.x t i e) =
      (∑ e, b e * M.x (Function.update t i b) i e) - (∑ e, b e * M.x t i e)
      - (∑ e, t i e * M.x (Function.update t i b) i e) + ∑ e, t i e * M.x t i e := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]; ring
  rw [this]
  linarith

lemma Q_ge {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (i : Fin (n' + 1)) (k : Fin ℓ) {lam u c : ℝ} (hl : 0 ≤ lam) (hu : 0 ≤ u)
    (hc : 0 ≤ c) (hcu : c < u) :
    ∑ a, M.x (Iu i k lam u) i (ee i k a) ≤ ∑ a, M.x (Is i k lam u c) i (ee i k a) := by
  have hw := wmon M htruth (Iu i k lam u) i (rowc i k c) (graph_Iu i k hl hu) (graph_Is i k hl hu hc)
  have e1 : ∀ e, (rowc i k c e - Iu i k lam u i e) *
        (M.x (Function.update (Iu i k lam u) i (rowc i k c)) i e - M.x (Iu i k lam u) i e) =
      rowc i k c e * (M.x (Is i k lam u c) i e - M.x (Iu i k lam u) i e) -
      Iu i k lam u i e * (M.x (Is i k lam u c) i e - M.x (Iu i k lam u) i e) := by
    intro e; unfold Is; ring
  simp only [e1, Finset.sum_sub_distrib, sum_row, sum_Iu] at hw
  rw [x_loop M hfeas hel _ (graph_Is i k hl hu hc) i, x_loop M hfeas hel _ (graph_Iu i k hl hu) i] at hw
  by_contra h
  push_neg at h
  nlinarith

lemma load_ge {n' ℓ : ℕ} (M : FracMech (n' + 1) (CoreTask (n' + 1) ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (hel : IsEligible M)
    (i : Fin (n' + 1)) (k : Fin ℓ) {lam u c : ℝ} (hl : 0 ≤ lam) (hu : 0 ≤ u) (hc : 0 ≤ c) :
    1 + c * ∑ a, M.x (Is i k lam u c) i (ee i k a) ≤ makespan M (Is i k lam u c) := by
  have h := Finset.le_sup' (fun m => ∑ j, Is i k lam u c m j * M.x (Is i k lam u c) m j)
    (Finset.mem_univ i)
  have e : ∑ j, Is i k lam u c i j * M.x (Is i k lam u c) i j =
      1 + c * ∑ a, M.x (Is i k lam u c) i (ee i k a) := by
    have := sum_row i k c (M.x (Is i k lam u c) i)
    rw [x_loop M hfeas hel _ (graph_Is i k hl hu hc) i] at this
    simpa [Is] using this
  unfold makespan
  rw [← e]
  exact h

open Classical in
noncomputable def sig {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) : CoreTask (n' + 1) ℓ → Fin (n' + 1) :=
  fun e => if h : ∃ a, ee i k a = e then i.succAbove (Classical.choose h)
    else if incident i e then i else Sum.elim (fun q => q.1.1.1) id e

lemma sig_ee {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (a : Fin n') :
    sig i k (ee i k a) = i.succAbove a := by
  have h : ∃ b, ee i k b = ee i k a := ⟨a, rfl⟩
  unfold sig
  rw [dif_pos h]
  rw [ee_inj i k (Classical.choose_spec h)]

lemma sig_notS {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {e : CoreTask (n' + 1) ℓ} (h : e ∉ SS i k) :
    sig i k e = if incident i e then i else Sum.elim (fun q => q.1.1.1) id e := by
  unfold sig
  rw [dif_neg]
  intro h'; exact h ((mem_SS i k e).2 h')

lemma sig_elig {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) (e : CoreTask (n' + 1) ℓ) :
    incident (sig i k e) e := by
  by_cases h : e ∈ SS i k
  · obtain ⟨a, rfl⟩ := (mem_SS i k e).1 h
    rw [sig_ee]; exact ee_inc_leaf i k a
  · rw [sig_notS i k h]
    split_ifs with h2
    · exact h2
    · rcases e with q | m
      · simp [incident]
      · simp [incident]

lemma C_le {n' ℓ : ℕ} (i : Fin (n' + 1)) (k : Fin ℓ) {lam u c : ℝ} (hl : 1 ≤ lam) (hu : 0 ≤ u)
    (hc : 0 ≤ c) : C (Is i k lam u c) ≤ lam := by
  have hmem : sig i k ∈ (Finset.univ.filter (fun σ : CoreTask (n' + 1) ℓ → Fin (n' + 1) =>
      ∀ e, incident (σ e) e)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact sig_elig i k
  refine le_trans (Finset.inf'_le _ hmem) ?_
  unfold schedMakespan
  apply Finset.sup'_le
  intro m _
  by_cases hm : m = i
  · subst hm
    have hterm : ∀ j ∈ Finset.univ.filter (fun j => sig m k j = m),
        Is m k lam u c m j ≤ if j = Sum.inr m then 1 else 0 := by
      intro j hj
      simp only [Is, Function.update_self, rowc]
      by_cases h1 : j = Sum.inr m
      · simp [h1]
      · by_cases h2 : j ∈ SS m k
        · exfalso
          obtain ⟨a, rfl⟩ := (mem_SS m k j).1 h2
          have := (Finset.mem_filter.1 hj).2
          rw [sig_ee] at this
          exact Fin.succAbove_ne m a this
        · simp [h1, h2]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_ite_eq']
    split_ifs <;> linarith
  · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hm
    have hterm : ∀ j ∈ Finset.univ.filter (fun j => sig i k j = i.succAbove a),
        Is i k lam u c (i.succAbove a) j ≤ if j = ee i k a then lam else 0 := by
      intro j hj
      have hsig := (Finset.mem_filter.1 hj).2
      simp only [Is, Function.update_of_ne hm, Iu_other i _ hm]
      by_cases h1 : j = ee i k a
      · simp only [h1, if_true]
        split_ifs <;> linarith
      · rw [if_neg h1]
        split_ifs with hcond
        · exfalso
          by_cases h2 : j ∈ SS i k
          · obtain ⟨b, rfl⟩ := (mem_SS i k j).1 h2
            rw [sig_ee] at hsig
            exact h1 (by rw [Fin.succAbove_right_injective hsig])
          · rw [sig_notS i k h2, if_pos hcond.2.1] at hsig
            exact Fin.succAbove_ne i a hsig.symm
        · exact le_refl _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_ite_eq']
    split_ifs <;> linarith

lemma C_nonneg {n' ℓ : ℕ} (t : Fin (n' + 1) → CoreTask (n' + 1) ℓ → ℝ) (ht : IsGraphInput t) :
    0 ≤ C t := by
  unfold C
  apply Finset.le_inf'
  intro σ _
  unfold schedMakespan
  exact Finset.le_sup'_of_le _ (Finset.mem_univ 0)
    (Finset.sum_nonneg (fun j _ => (ht 0 j).1))

end Dev.StarB2
open Dev.StarB2 FracTruthSched.Dev.StarA FracTruthSched.Dev.StarB1

theorem chk_star_bound {n ℓ : ℕ} [NeZero n] (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) (ρ : ℝ)
    (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (huz : HasUniqueZeros M) (hzti : HasZeroTypeIrrelevance M)
    (hsym : IsClassSymmetric M) (hload : ∀ t, IsGraphInput t → makespan M t ≤ ρ * C t)
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ lam ∈ Set.Ioo 1 (1 + ε),
      1 + (c : ℝ) * ((n : ℝ) - 1) / 2 * (1 - 1 / (ℓ : ℝ)) ^ (n - 2) ≤ ρ * lam ∧
        ρ * lam ≤ ρ * (1 + ε) := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i, hi⟩ := pieceB1 hℓ M hfeas htruth hel hzti
  obtain ⟨lam, hlam, hAS⟩ := lemma_5 hℓ M hfeas htruth hel hzti hsym i ε hε
  have hc0' : (0 : ℝ) < c := by exact_mod_cast hc0
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast hc1
  have hl1 : 1 < lam := hlam.1
  set k0 : Fin ℓ := ⟨0, by omega⟩ with hk0
  set u : ℝ := ((c : ℝ) + 1) / 2 with hu
  have hcu : (c : ℝ) < u := by rw [hu]; linarith
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hqs := hi lam hl1.le
  have hA := pieceA hℓ M hfeas htruth i lam (by linarith)
    (fun j hj => (hAS j hj).1) (fun j hj => (hAS j hj).2) u ⟨by linarith, by rw [hu]; linarith⟩
  have hA' : (1 - 1 / (ℓ : ℝ)) ^ (n' - 1) * ∑ a : Fin n', M.x (rootStarInput i lam
        (Pi.single (E i (i.succAbove a) k0) 1)) i (E i (i.succAbove a) k0) ≤
      ∑ a, M.x (Iu i k0 lam u) i (ee i k0 a) := hA
  have hfac : 0 ≤ (1 - 1 / (ℓ : ℝ)) ^ (n' - 1) := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast (by omega : 1 ≤ ℓ)
  have hN : (1 - 1 / (ℓ : ℝ)) ^ (n' - 1) * ((n' : ℝ) / 2) ≤ ∑ a, M.x (Iu i k0 lam u) i (ee i k0 a) :=
    le_trans (mul_le_mul_of_nonneg_left hqs hfac) hA'
  have hQ := Q_ge M hfeas htruth hel i k0 (lam := lam) (by linarith) hu0 hc0'.le hcu
  have hLoad := load_ge M hfeas hel i k0 (lam := lam) (u := u) (c := (c : ℝ)) (by linarith) hu0 hc0'.le
  have hCle := C_le i k0 (lam := lam) (u := u) (c := (c : ℝ)) hl1.le hu0 hc0'.le
  have hg := graph_Is i k0 (lam := lam) (u := u) (c := (c : ℝ)) (by linarith) hu0 hc0'.le
  have hC0 := C_nonneg _ hg
  have hmk := hload _ hg
  have hNn : 0 ≤ ∑ a, M.x (Iu i k0 lam u) i (ee i k0 a) :=
    le_trans (mul_nonneg hfac (by positivity)) hN
  have hρ : 0 ≤ ρ := by
    by_contra h
    push Not at h
    have : ρ * C (Is i k0 lam u (c : ℝ)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le hC0
    have : 0 ≤ (c : ℝ) * ∑ a, M.x (Is i k0 lam u (c : ℝ)) i (ee i k0 a) :=
      mul_nonneg hc0'.le (le_trans hNn hQ)
    linarith
  have hρC : ρ * C (Is i k0 lam u (c : ℝ)) ≤ ρ * lam := mul_le_mul_of_nonneg_left hCle hρ
  have e1 : ((n' + 1 : ℕ) : ℝ) - 1 = n' := by push_cast; ring
  have e2 : n' + 1 - 2 = n' - 1 := by omega
  refine ⟨lam, hlam, ?_, mul_le_mul_of_nonneg_left hlam.2.le hρ⟩
  rw [e1, e2]
  have : (c : ℝ) * (n' : ℝ) / 2 * (1 - 1 / (ℓ : ℝ)) ^ (n' - 1) ≤
      (c : ℝ) * ∑ a, M.x (Iu i k0 lam u) i (ee i k0 a) := by
    calc _ = (c : ℝ) * ((1 - 1 / (ℓ : ℝ)) ^ (n' - 1) * ((n' : ℝ) / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN hc0'.le
  have : (c : ℝ) * ∑ a, M.x (Iu i k0 lam u) i (ee i k0 a) ≤
      (c : ℝ) * ∑ a, M.x (Is i k0 lam u (c : ℝ)) i (ee i k0 a) :=
    mul_le_mul_of_nonneg_left hQ hc0'.le
  linarith


end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_star_bound := @FracTruthSched.chk_star_bound
